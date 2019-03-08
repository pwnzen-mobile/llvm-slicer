#include <string>
#include <set>

using namespace std;

namespace llvm {
namespace dfa {
    class MethodFeature{
    public:
        MethodFeature(string name){};
    private:
        string name;
        
        void setName(string name);
        string getName();
    };

    class MethodSummary {
    public:
        set<MethodFeature> SideEffectSet;
        set<MethodFeature> PreConditionsSet;
        set<MethodFeature> PostConditionsSet;
    

    };
}
}