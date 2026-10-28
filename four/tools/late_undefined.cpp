// Untrusted first-undefined search. Coq must replay each reported prefix before
// joining all sixteen defined choices and the separate halting choice.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
array<int,8> parse(const string& s) {
  if(s.size()!=25 || s[12]!='_')throw runtime_error("Invalid machine");
  array<int,8> a{};
  for(int i=0;i<8;i++){
    int p=3*i+(i>=4);
    if(s.substr(p,3)=="---"){a[i]=16;continue;}
    if(s[p]<'0'||s[p]>'3'||(s[p+1]!='L'&&s[p+1]!='R')||(s[p+2]!='A'&&s[p+2]!='B'))throw runtime_error("Invalid transition");
    a[i]=4*(s[p]-'0')+2*(s[p+1]=='R')+(s[p+2]=='B');
  }
  return a;
}
int main(int argc,char**argv){
 try{
  if(argc!=4)throw runtime_error("usage: late_undefined INPUT OUTPUT_TSV FUEL");
  int fuel=stoi(argv[3]);if(fuel<1||fuel>100000000)throw runtime_error("Invalid fuel");
  ifstream in(argv[1]);ofstream out(argv[2]);if(!in||!out)throw runtime_error("Cannot open files");
  vector<unsigned char> tape(2*fuel+5);int origin=fuel+2,oldlo=origin,oldhi=origin;
  string machine;long long steps=0;int rows=0,found=0;
  auto start=chrono::steady_clock::now();
  out<<"machine\tstatus\tanchor\tcell\tposition\tspan\n";
  while(getline(in,machine)){
   auto tm=parse(machine);if(count(tm.begin(),tm.end(),16)==0)throw runtime_error("Expected partial table");
   fill(tape.begin()+oldlo,tape.begin()+oldhi+1,0);
   int q=0,pos=origin,lo=pos,hi=pos,n=0,slot=0;
   for(;n<fuel;n++){
    slot=4*q+tape[pos];int v=tm[slot];if(v==16)break;
    tape[pos]=v/4;q=v%2;pos+=(v&2)?1:-1;lo=min(lo,pos);hi=max(hi,pos);
   }
   slot=4*q+tape[pos];bool hit=tm[slot]==16;found+=hit;steps+=n;rows++;oldlo=lo;oldhi=hi;
   out<<machine<<'\t'<<(hit?"reached_undefined":"budget_exhausted")<<'\t'<<n<<'\t'<<(hit?slot:-1)<<'\t'<<pos-origin<<'\t'<<hi-lo+1<<'\n';
  }
  cout<<"{\"families\":"<<rows<<",\"reached_undefined\":"<<found<<",\"steps\":"<<steps<<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"}\n";
 }catch(const exception&e){cerr<<e.what()<<'\n';return 2;}
}
