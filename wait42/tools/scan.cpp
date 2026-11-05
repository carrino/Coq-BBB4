// Untrusted finite observation search. A missing visit is never a silence proof.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

constexpr uint64_t missing = std::numeric_limits<uint64_t>::max();
struct Transition { int write, move, next; };
using Machine = std::array<Transition, 8>;

Machine parse(const std::string &s) {
  if (s.size() != 27) throw std::runtime_error("expected four binary rows");
  Machine m{};
  for (int q=0;q<4;++q) for (int a=0;a<2;++a) {
    int j=7*q+3*a;
    if (q<3 && s[7*q+6]!='_') throw std::runtime_error("bad row separator");
    if (s.substr(j,3)=="---") { m[2*q+a]={0,1,-1}; continue; }
    if ((s[j]!='0' && s[j]!='1') || (s[j+1]!='L' && s[j+1]!='R') ||
        s[j+2]<'A' || s[j+2]>'D') throw std::runtime_error("bad transition");
    m[2*q+a]={s[j]-'0',s[j+1]=='R'?1:-1,s[j+2]-'A'};
  }
  return m;
}

bool closed_states(const Machine &m, unsigned seen) {
  for (int k=0;k<8;++k)
    if ((seen&(1u<<(k/2))) && m[k].next>=0 && !(seen&(1u<<m[k].next))) return false;
  return true;
}
bool closed_instructions(const Machine &m, unsigned seen) {
  for (int k=0;k<8;++k) if ((seen&(1u<<k)) && m[k].next>=0) {
    unsigned next=3u<<(2*m[k].next);
    if ((seen&next)!=next) return false;
  }
  return true;
}
template<size_t N> void array_json(const std::array<uint64_t,N> &a) {
  std::cout<<'[';
  for (size_t i=0;i<N;++i) { if(i)std::cout<<','; if(a[i]==missing)std::cout<<"null";else std::cout<<a[i]; }
  std::cout<<']';
}

int main(int argc,char **argv) {
  try {
    if(argc!=4) throw std::runtime_error("usage: scan START CAP state|instruction");
    uint64_t begin=std::stoull(argv[1]), cap=std::stoull(argv[2]);
    std::string mode=argv[3];
    if(cap<begin || (mode!="state" && mode!="instruction")) throw std::runtime_error("invalid bounds or mode");
    constexpr int cells=1<<24;
    std::vector<uint8_t> tape(cells);
    std::string s;
    while(std::getline(std::cin,s)) {
      if(s.empty())continue;
      auto m=parse(s); std::fill(tape.begin(),tape.end(),0);
      std::array<uint64_t,4> st; st.fill(missing);
      std::array<uint64_t,8> ins; ins.fill(missing);
      unsigned sm=0,im=0; int pos=cells/2,q=0;
      uint64_t state_closed_at=missing,instr_closed_at=missing,t=0;
      std::string status="cap";
      for(;;) {
        int k=2*q+tape[pos];
        if(t>=begin) {
          bool changed_st=!(sm&(1u<<q)),changed_in=!(im&(1u<<k));
          if(changed_st) {st[q]=t;sm|=1u<<q;}
          if(changed_in) {ins[k]=t;im|=1u<<k;}
          if(changed_st && state_closed_at==missing && closed_states(m,sm)) state_closed_at=t;
          if(changed_in && instr_closed_at==missing && closed_instructions(m,im)) instr_closed_at=t;
          if((mode=="state" && state_closed_at!=missing) || instr_closed_at!=missing) {status="closed-control-mask";break;}
        }
        if(m[k].next<0) {status="halt";break;}
        if(t==cap)break;
        auto tr=m[k];tape[pos]=tr.write;pos+=tr.move;q=tr.next;++t;
        if(pos<0 || pos>=cells) {status="edge";break;}
      }
      std::cout<<"{\"machine\":\""<<s<<"\",\"start\":"<<begin<<",\"cap\":"<<cap
               <<",\"stopped_at\":"<<t<<",\"status\":\""<<status<<"\",\"state_first\":";
      array_json(st); std::cout<<",\"instruction_first\":";array_json(ins);
      std::cout<<",\"state_control_closed_at\":";
      if(state_closed_at==missing)std::cout<<"null";else std::cout<<state_closed_at;
      std::cout<<",\"instruction_control_closed_at\":";
      if(instr_closed_at==missing)std::cout<<"null";else std::cout<<instr_closed_at;
      std::cout<<"}\n"<<std::flush;
    }
  } catch(const std::exception &e) {std::cerr<<e.what()<<'\n';return 2;}
}
