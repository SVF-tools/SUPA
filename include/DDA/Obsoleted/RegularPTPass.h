/*
 * RegularPTPASS.h
 *
 *  Created on: May 14, 2013
 *      Author: rocky
 */

#ifndef REGULARPTPASS_H_
#define REGULARPTPASS_H_

#include "MemoryModel/PointerAnalysis.h"
#include <llvm/PassAnalysisSupport.h>

/*!
 *	Demand-Driven Points-to Analysis for Java (OOPSLA '05)
 */
class RegularPTPass: public PointerAnalysis, public llvm::ModulePass {
protected:
    typedef std::map<NodeID, PointsTo> PointsToMap;
    typedef PointsToMap AliasSetMap;
    AliasSetMap nodeToAliasMap; ///< Node to its aliases map
    PointsToMap ptsCache;
    NodePairSet aliasCheckPairs;	// recur aliasing check map
    NodePairSet nodeMatchCache;		// load store match map
    PAGEdge::PAGEdgeToSetMapTy candidateStoresMap;// caching each load to a set of candidate stores for alias checking
    Size_t stepNum;
    bool earlyTerminate;
    /// reset the data for next round query
    void resetStatePerQuery();

public:
    static char ID;

    RegularPTPass(char id = ID) :
        PointerAnalysis(PointerAnalysis::Regular_DDA), ModulePass(ID), stepNum(0), earlyTerminate(false) {
    }

    virtual bool runOnModule(llvm::Module& module);

    /// Adjust pointer for answering alias queries(redirect the virtual pointer),
    /// do not place it into its super class
    virtual void *getAdjustedAnalysisPointer(llvm::AnalysisID PI) {
        if (PI == &AliasAnalysis::ID)
            return (AliasAnalysis*)this;
        return this;
    }

    /// Get alias set from llvm value
    inline AliasSet& getAliasSet(const llvm::Value* val) {
        return getAliasSet(pag->getValueNode(val));
    }
    /// Get alias set from PAG node
    inline AliasSet& getAliasSet(NodeID id) {
        return nodeToAliasMap[id];
    }

    //@{ Methods for support type inquiry through isa, cast, and dyn_cast:
    static inline bool classof(const RegularPTPass *) {
        return true;
    }
    static inline bool classof(const PointerAnalysis *pta) {
        return pta->getAnalysisTy() == PointerAnalysis::Regular_DDA;
    }
    //@}

    /// analysis
    virtual void analyze(llvm::Module& module);

    /// get total number of query in the program
    Size_t getTotalNumberOfQuery();

    /// check whether exceeding the budget we set
    bool checkEarlyTemination();

    ///Demand-Driven Points-to Analysis for Java (OOPSLA '05)
    //@{
    PointsTo regularPT(NodeID nodeId);

    void propagate(NodeID nodeId, NodeList &worklist, NodeSet& markedSet);

    void matchLoadStore(PAGEdge* load, NodeList &worklist, NodeSet& markedSet);
    //@}

    /// component methods to avoid recursive alias checking
    //@{
    bool checkRecurAliasing(NodeID loadSrc, NodeID storeDst) {
        if (aliasCheckPairs.find(std::make_pair(loadSrc, storeDst))
                != aliasCheckPairs.end())
            return true;
        else
            return false;
    }

    void addCheckRecurAliasing(NodeID loadSrc, NodeID storeDst) {
        aliasCheckPairs.insert(std::make_pair(loadSrc, storeDst));
    }

    void removeCheckRecurAliasing(NodeID loadSrc, NodeID storeDst) {
        aliasCheckPairs.erase(std::make_pair(loadSrc, storeDst));
    }
    //@}

    /// component methods for caching, record the match edge
    //@{
    void addToMatchCache(NodeID loadDst, NodeID storeSrc) {
        nodeMatchCache.insert(std::make_pair(loadDst, storeSrc));
    }

    bool checkMatchCache(NodeID loadDst, NodeID storeSrc) {
        if (nodeMatchCache.find(std::make_pair(loadDst, storeSrc))
                != nodeMatchCache.end())
            return true;
        else
            return false;
    }
    //@}

    /// dump the alias set of each pointer
    void dumpAliasSetWithPointsToMap();

    const char* getPassName() const {
        return " RegularPTPass";
    }

    virtual inline PointsTo& getPts(NodeID id) {
        return getAliasSet(id);
    }

    /// Interface expose to users of our pointer analysis, given Location infos
    virtual AliasAnalysis::AliasResult alias(const AliasAnalysis::Location &LocA,
            const AliasAnalysis::Location &LocB) {
        return AliasAnalysis::MayAlias;
    }

    /// Interface expose to users of our pointer analysis, given Value infos
    virtual AliasAnalysis::AliasResult alias(const llvm::Value* V1,
            const llvm::Value* V2) {
        return AliasAnalysis::MayAlias;
    }
};

/*!
 *	Refinement-Based Context Sensitive Points-to Analysis for Java (PLDI '06)
 */
class RefinePTPass: public RegularPTPass {

public:
    static char ID;

    RefinePTPass() :
        RegularPTPass(ID) {
    }

    bool runOnModule(llvm::Module& module);

    /// analysis
    virtual void analyze(llvm::Module& module);

    //@{
    void findPointsTo(NodeID nodeId, NodeBS &visited, PointsTo& pts);

    void matchLoadWithStore(PointsTo &pts, PAGEdge* load, NodeBS &markedSet);

    void refineStoreEdgeSearch(PAGEdge* load);
    //@}

};

#endif /* REGULARPTPASS_H_ */
