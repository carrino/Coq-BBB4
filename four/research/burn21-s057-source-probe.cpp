#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
int main(int argc,char**argv){
 if(argc!=4)return 2;uint64_t budget=stoull(argv[3]);ifstream in(argv[1]);ofstream out(argv[2]);string machine;
 while(getline(in,machine)){
  if(machine.size()!=25||machine[12]!='_')throw runtime_error("bad table");array<int,8> tm;
  for(int i=0;i<8;i++){int j=3*i+(i>=4);if(machine[j]<'0'||machine[j]>'3'||(machine[j+1]!='L'&&machine[j+1]!='R')||(machine[j+2]!='A'&&machine[j+2]!='B'))throw runtime_error("bad entry");tm[i]=4*(machine[j]-'0')+2*(machine[j+1]=='R')+(machine[j+2]=='B');}
  int origin=1<<19;vector<unsigned char> tape(2*origin);int p=0,q=0,lo=0,hi=-1;uint64_t last[2]={0,0},maxrun[2]={0,0},run=0,t=0;bool escaped=false;
  auto start=chrono::steady_clock::now();
  for(;t<budget;t++){
   last[q]=t;run++;maxrun[q]=max(maxrun[q],run);
   if(q==1&&p>hi&&(tm[4]&3)==3){escaped=true;break;}
   int cell=p+origin;
   if(cell<1||cell+1>=int(tape.size())){int old=origin;origin*=2;vector<unsigned char> bigger(2*origin);copy(tape.begin(),tape.end(),bigger.begin()+origin-old);tape.swap(bigger);cell=p+origin;}
   int tr=tm[4*q+tape[cell]],w=tr/4,nq=tr&1;tape[cell]=w;
   if(w){if(lo>hi){lo=hi=p;}else{lo=min(lo,p);hi=max(hi,p);}}else{if(p==lo)while(lo<=hi&&!tape[origin+lo])lo++;if(p==hi)while(hi>=lo&&!tape[origin+hi])hi--;}
   if(nq!=q)run=0;q=nq;p+=(tr&2)?1:-1;
  }
  out<<"{\"machine\":\""<<machine<<"\",\"steps\":"<<t<<",\"right_blank_B_escape\":"<<(escaped?"true":"false")<<",\"state\":"<<q<<",\"position\":"<<p<<",\"nonzero_span\":["<<lo<<","<<hi<<"],\"last_visits\":["<<last[0]<<","<<last[1]<<"],\"max_episodes\":["<<maxrun[0]<<","<<maxrun[1]<<"],\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"}\n";out.flush();
 }
}
