/*
 // Flow Insensitive and Context Insensitive Demand-Driven Points-to and Alias Analysis Pass
 // 1) reference: Demand-Driven Points-to Analysis for Java (OOPSLA '05)
 // 2) reference: Refinement-Based Context Sensitive Points-to Analysis for Java (PLDI' 06)
 // 3) reference: Demand-Driven Alias Anlaysis For C (POPL '08)
 // Author: Yulei Sui,
 */

#ifndef DAAPASS_H
#define DAAPASS_H

#include "MemoryModel/PointerAnalysis.h"
#include "Util/DataFlowUtil.h"

struct DPTItem {

    enum State {
        S0,  // initial(dummy) state
        S1,  // inverse flow
        S2,  // address node
        S3   // forward flow
    };

    NodeID cur;
    NodeID root;
    State state;
    NodeVector field;
    NodeVector context;

    DPTItem(NodeID c, NodeID r, State s) :
        cur(c), root(r), state(s) {
    }

    DPTItem(NodeID c, NodeID r, State s, NodeVector v, NodeVector w) :
        cur(c), root(r), state(s), field(v), context(w) {
    }

    DPTItem(const DPTItem& dps) :
        cur(dps.cur), root(dps.root), state(dps.state), field(dps.field), context(
            dps.context) {
    }

    /// enable compare operator to avoid duplicated item insertion in map or set
    /// to be noted that two vectors can also use operator < or > for comparision
    typedef struct {
        bool operator()(const DPTItem &lhs, const DPTItem &rhs) {
            if (lhs.cur != rhs.cur)
                return lhs.cur < rhs.cur;
            else if (lhs.root != rhs.root)
                return lhs.root < rhs.root;
            else
                // if(lhs.state != rhs.state)
                return lhs.state < rhs.state;
            /// FIXME: do we need to compare this? if these two fields are empty, then we may end up with wrong comparision
//        	else if(lhs.field != rhs.field)
//        	    return lhs.field < rhs.field;
//        	else
//        		return lhs.context < rhs.context;
        }
    } equalDPTItem;
};

/*!
 * Demand-Driven Alias Anlaysis For C (POPL '08)
 */
class DAAPass: public PointerAnalysis, public llvm::ModulePass {

protected:
    // this map type is used to map each node with pairs :(root,state)
    // to avoid recursive traversal
    typedef std::map<NodeID, PointsTo> PointsToMap;
    typedef PointsToMap AliasSetMap;
    typedef std::set<DPTItem, DPTItem::equalDPTItem> DPTItemSet;
    typedef llvm::DenseMap<NodeID, NodePairSet> NodeToReachPairsMap;
    typedef llvm::DenseMap<NodeID, DPTItemSet> NodeToDPTItemMap;
    AliasSetMap nodeToAliasMap; ///< Node to its aliases map
    PointsToMap ptsCache;
    NodeToDPTItemMap nodesVisited;
    AliasSetMap MatchLDSrcToSTdstMap;// record the matching load -- > store edge for S1
    AliasSetMap MatchSTdstToLDsrcMap;// record the matching store -- > load edge for S3
    std::list<DPTItem> worklist;  // worklist for DPT item

    Size_t stepNum;
    bool earlyTerminate;

public:
    static char ID;

    DAAPass(char id = ID, PointerAnalysis::PTATY ty = PointerAnalysis::Insensitive_DDA) :
        PointerAnalysis(ty),  ModulePass(ID),  stepNum(0), earlyTerminate(false) {
    }

    virtual ~DAAPass() {
        delete pag;
        pag = NULL;
    }
    /// we start from here
    virtual bool runOnModule(SVFModule module);

    /// Adjust pointer for answering alias queries(redirect the virtual pointer),
    /// do not place it into its super class
    virtual void *getAdjustedAnalysisPointer(llvm::AnalysisID PI) {
        if (PI == &AliasAnalysis::ID)
            return (AliasAnalysis*)this;
        return this;
    }
    /// LLVM analysis usage
    virtual void getAnalysisUsage(llvm::AnalysisUsage& au) const {
        /// do not intend to change the IR in this pass,
        au.setPreservesAll();
    }
    /// DDA analysis
    virtual void analyze(SVFModule module);

    //@{ Methods for support type inquiry through isa, cast, and dyn_cast:
    static inline bool classof(const DAAPass *) {
        return true;
    }
    static inline bool classof(const PointerAnalysis *pta) {
        return pta->getAnalysisTy() == PointerAnalysis::Insensitive_DDA ||
               pta->getAnalysisTy() == PointerAnalysis::FieldS_DDA ||
               pta->getAnalysisTy() == PointerAnalysis::Cxt_DDA ||
               pta->getAnalysisTy() == PointerAnalysis::FlowS_DDA ;
    }
    //@}

    /// Get alias set from llvm value
    inline AliasSet& getAliasSet(const llvm::Value* val) {
        return getAliasSet(pag->getValueNode(val));
    }
    /// Get alias set from PAG node
    inline AliasSet& getAliasSet(NodeID id) {
        return nodeToAliasMap[id];
    }

    /// reset the data for next round query
    virtual void resetStatePerQuery();

    /// get total number of query in the program
    Size_t getTotalNumberOfQuery();

    /// check whether exceeding the budget we set
    bool checkEarlyTemination();

    /// add alias relation between two nodes (both point to the same memory location)
    void addToAliasSet(NodeID root, NodeID tgr);

    /// return true if two pointers point to at least one common memory location
    bool isAlias(NodeID node1, NodeID node2);

    /// match loads with stores (loadDst with StoreSrc)
    void addToNodeMatchMap(NodeID loadDst, NodeID storeSrc);

    /// given loadSrc, return all matched storeDst
    AliasSet& getMatchSTdstFromLDsrc(NodeID cur);

    /// given storeDst, return all matched loadSrc
    AliasSet& getMatchLDsrcFromSTdst(NodeID cur);

    /// match load/store for direct propagate from S1-->S1 or S3-->S3
    void MatchLoadStore(DPTItem& origItem, NodeID cur,
                        DPTItem::State propState);

    /// enable cache
    void enableCache(NodeID root);

    /// reuse cache
    bool reuseCache(NodeID node, NodeID root, DPTItem::State);

    /// computing all aliases of this pointer
    void computeAlias(NodeID node);

    /// vitual methods can be used for child class
    //@{
    /// propagate alias upwards, from alias to S1 or S3
    virtual void propAliasUpwards(DPTItem& item);

    virtual void propAliasUpToInverseFlow(DPTItem& item);

    virtual void propAliasUpToDirectFlow(DPTItem& item);

    /// goes into another level of alias search
    virtual void propAliasDownwards(DPTItem& item);

    /// propagate the state following recursive state machine
    virtual void stateProp(const DPTItem& item, NodeID propNode,
                           DPTItem::State propState, PAGEdge *gepOrCallRetEdge = NULL);
    //}@

    /// we will refactor this method later
    void stateProp(NodeID root, NodeID node, DPTItem::State state);

    /// handle three status in recursive state machine
    //@{
    void handleS1(DPTItem& item);

    void handleS2(DPTItem& item);

    void handleS3(DPTItem& item);

    //@}

    virtual const char* getPassName() const {
        return " DAAPass";
    }

    virtual inline PointsTo& getPts(NodeID id) {
        return getAliasSet(id);
    }

    virtual const std::string PTAName() const {
        return "DDA";
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
 * Field sensitive version of DAA analysis
 */
class FieldDAAPass: public DAAPass {

protected:
    NodeToDPTItemMap savedS1States; // save the state before propagate down in S1
    NodeToDPTItemMap savedS3States; // save the state before propagate down in S3
public:

    static char ID;

    FieldDAAPass(char id = ID, PointerAnalysis::PTATY ty = PointerAnalysis::FieldS_DDA) :
        DAAPass(ID, ty) {
    }

    //@{ Methods for support type inquiry through isa, cast, and dyn_cast:
    static inline bool classof(const FieldDAAPass *) {
        return true;
    }
    static inline bool classof(const DAAPass *pta) {
        return pta->getAnalysisTy() == PointerAnalysis::FieldS_DDA ||
               pta->getAnalysisTy() == PointerAnalysis::Cxt_DDA ||
               pta->getAnalysisTy() == PointerAnalysis::FlowS_DDA;
    }
    static inline bool classof(const PointerAnalysis *pta) {
        return llvm::isa<DAAPass>(pta)
               && classof(llvm::cast<DAAPass>(pta));
    }
    //@}
    /// overriding methods state propagation
    /// explicitly use another stateProp method if necessary (using DAAPass::stateProp) to avoid hidden it.
    virtual void stateProp(const DPTItem& item, NodeID propNode,
                           DPTItem::State propState, PAGEdge *gepOrCallRetEdge = NULL);

    /// overriding functions for reset information per query
    virtual void resetStatePerQuery();

    /// overriding methods for propagate state downwards and upwards
    /// actually they have the same functionality as the parent class, but implemented in another way.
    //@{
    virtual void propAliasDownwards(DPTItem& item);

    virtual void propAliasUpToInverseFlow(DPTItem& item);

    virtual void propAliasUpToDirectFlow(DPTItem& item);
    // @}

    /// overriding methods for normal pass properties
    //@{
    const char* getPassName() const {
        return "FiledDAAPass";
    }

    void getAnalysisUsage(llvm::AnalysisUsage& au) const {
        /// do not intend to change the IR in this pass,
        au.setPreservesAll();
    }
    //@}

    virtual bool dyckCFLParentheseMatch(const DPTItem& origItem,
                                        NodeVector &stack, DPTItem::State propState,
                                        PAGEdge *gepOrCallRetEdge = NULL);

    /// figure out whether this state transition needs to push field (S1-->S1 with inverse gep edge)
    bool inverseFieldStateTransition(const DPTItem& item,
                                     DPTItem::State propState, Size_t offset);

    /// figure out whether this state transition needs to match field (S3-->S3 with direct gep edge)
    bool directFieldStateTransition(const DPTItem& item,
                                    DPTItem::State propState, Size_t offset);

    virtual const std::string PTAName() const {
        return "FieldDDA";
    }
};

/*!
 * Context sensitive version of DAA analysis
 */
class ContextDAAPass: public FieldDAAPass {

public:
    static char ID;

    ContextDAAPass(char id = ID, PointerAnalysis::PTATY ty = PointerAnalysis::Cxt_DDA) :
        FieldDAAPass(id, ty) {
    }

    //@{ Methods for support type inquiry through isa, cast, and dyn_cast:
    static inline bool classof(const ContextDAAPass *) {
        return true;
    }
    static inline bool classof(const FieldDAAPass *pta) {
        return pta->getAnalysisTy() == PointerAnalysis::Cxt_DDA;
    }
    static inline bool classof(const DAAPass *pta) {
        return llvm::isa<FieldDAAPass>(pta)
               && classof(llvm::cast<FieldDAAPass>(pta));
    }
    static inline bool classof(const PointerAnalysis *pta) {
        return llvm::isa<DAAPass>(pta)
               && classof(llvm::cast<DAAPass>(pta));
    }
    //@}
    /// overriding methods state propagation
    /// explicitly use another stateProp method if necessary (using DAAPass::stateProp) to avoid hidden it.
    virtual void stateProp(const DPTItem& item, NodeID propNode,
                           DPTItem::State propState, PAGEdge *gepOrCallRetEdge = NULL);

    virtual bool dyckCFLParentheseMatch(const DPTItem& origItem,
                                        NodeVector &stack, DPTItem::State propState,
                                        PAGEdge *gepOrCallRetEdge = NULL);

    virtual const std::string PTAName() const {
        return "ContextDDA";
    }
};

/*!
 * Flow sensitive version of DAA analysis
 */
class FlowDAAPass: public FieldDAAPass {

public:
    static char ID;

    FlowDAAPass(char id = ID, PointerAnalysis::PTATY ty = PointerAnalysis::FlowS_DDA) :
        FieldDAAPass(id, ty) {
    }

    //@{ Methods for support type inquiry through isa, cast, and dyn_cast:
    static inline bool classof(const FlowDAAPass *) {
        return true;
    }
    static inline bool classof(const FieldDAAPass *pta) {
        return pta->getAnalysisTy() == PointerAnalysis::FlowS_DDA;
    }
    static inline bool classof(const DAAPass *pta) {
        return llvm::isa<FieldDAAPass>(pta)
               && classof(llvm::cast<FieldDAAPass>(pta));
    }
    static inline bool classof(const PointerAnalysis *pta) {
        return llvm::isa<DAAPass>(pta)
               && classof(llvm::cast<DAAPass>(pta));
    }
    //@}
    bool runOnModule(SVFModule module);

    virtual void getAnalysisUsage(llvm::AnalysisUsage& au) const {
        au.addRequired<IteratedDominanceFrontier>();
        /// do not intend to change the IR in this pass,
        au.setPreservesAll();
    }

    virtual const std::string PTAName() const {
        return "FlowDDA";
    }
};

#endif
