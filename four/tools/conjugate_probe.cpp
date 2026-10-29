// Untrusted search for intersecting head-relative blank-start trajectories.
// Run the SAME table from A and B. Hash hits must be checked by an exact finite
// tape comparison and then a Coq transport checker; this program proves nothing.
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_map>
#include <vector>

struct Trans { int write, move, next; bool defined; };
struct Key {
  uint64_t a,b; int state;
  bool operator==(const Key& x) const {return a==x.a && b==x.b && state==x.state;}
};
struct KeyHash {
  size_t operator()(const Key& k) const {
    return k.a ^ ((k.b<<17)|(k.b>>47)) ^ (uint64_t(k.state)*0x9e3779b97f4a7c15ULL);
  }
};
uint64_t inverse(uint64_t a) {
  uint64_t x=1;
  for(int i=0;i<6;++i) x*=2-a*x;
  return x;
}
struct Run {
  std::vector<int> tape; int pos,state; uint64_t a=0,b=0;
  Run(int fuel,int initial):tape(2*fuel+3),pos(fuel+1),state(initial) {}
  Key key() const {return {a,b,state};}
  bool step(const Trans* tm) {
    const auto& tr=tm[4*state+tape[pos]];
    if(!tr.defined) return false;
    const uint64_t base1=1315423911ULL,base2=11400714819323198485ULL;
    static const uint64_t inv1=inverse(base1),inv2=inverse(base2);
    uint64_t delta=uint64_t(tr.write)-uint64_t(tape[pos]);
    a=(a+delta)*(tr.move==1 ? inv1:base1);
    b=(b+delta)*(tr.move==1 ? inv2:base2);
    tape[pos]=tr.write;pos+=tr.move;state=tr.next;return true;
  }
};
int main(int argc,char** argv) {
  if(argc!=3) {std::cerr<<"usage: conjugate_probe fuel input.txt\n";return 2;}
  int fuel=std::stoi(argv[1]);
  if(fuel<0 || fuel>1000000) return 2;
  std::ifstream input(argv[2]);
  if(!input) return 2;
  std::cout<<"machine\tstatus\ttarget_boot\tsource_boot\tb_halted\n";
  std::string machine;
  while(std::getline(input,machine)) {
    if(machine.empty()) continue;
    std::string raw;for(char c:machine) if(c!='_') raw+=c;
    if(raw.size()!=24) return 2;
    Trans tm[8];
    for(int i=0;i<8;++i) {
      std::string cell=raw.substr(3*i,3);
      if(cell=="---") tm[i]={0,0,0,false};
      else {
        if(cell[0]<'0'||cell[0]>'3'||(cell[1]!='L'&&cell[1]!='R')||(cell[2]!='A'&&cell[2]!='B')) return 2;
        tm[i]={cell[0]-'0',cell[1]=='R'?1:-1,cell[2]-'A',true};
      }
    }
    std::unordered_map<Key,int,KeyHash> seen;seen.reserve(fuel+1);
    Run b(fuel,1);bool b_halted=false;
    for(int n=0;n<=fuel;++n) {
      seen.emplace(b.key(),n);
      if(n<fuel&&!b.step(tm)) {b_halted=true;break;}
    }
    Run a(fuel,0);bool found=false,halted=false;
    for(int n=0;n<=fuel;++n) {
      auto it=seen.find(a.key());
      if(it!=seen.end()) {
        std::cout<<machine<<"\tmatch\t"<<n<<"\t"<<it->second<<"\t"<<b_halted<<"\n";
        found=true;break;
      }
      if(n<fuel&&!a.step(tm)) {halted=true;break;}
    }
    if(!found) std::cout<<machine<<'\t'<<(halted?"halted":"no_match")<<"\t\t\t"<<b_halted<<"\n";
  }
}
