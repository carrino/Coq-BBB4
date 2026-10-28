// Untrusted reconnaissance for blank-tape re-rooting after a finite prefix.
// A completely blank tape is detected by an exact nonzero-cell count.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;

array<int,8> table(const string& text) {
  if(text.size()!=25 || text[12]!='_')throw runtime_error("Invalid table");
  array<int,8> result;
  for(int i=0;i<8;++i) {
    int j=3*i+(i>=4);
    if(text.substr(j,3)=="---") { result[i]=16; continue; }
    if(text[j]<'0'||text[j]>'3'||(text[j+1]!='L'&&text[j+1]!='R')
       ||(text[j+2]!='A'&&text[j+2]!='B'))throw runtime_error("Invalid transition");
    result[i]=4*(text[j]-'0')+2*(text[j+1]=='R')+(text[j+2]=='B');
  }
  return result;
}
int main(int argc,char** argv) {
  try {
    if(argc!=4)throw runtime_error("usage: blank_returns INPUT OUTPUT_TSV FUEL");
    int fuel=stoi(argv[3]);
    if(fuel<1||fuel>10000000)throw runtime_error("Invalid fuel");
    ifstream input(argv[1]);ofstream output(argv[2]);
    if(!input||!output)throw runtime_error("Cannot open input or output");
    output<<"machine\tanchor\tstate\tposition\n";
    vector<unsigned char> tape(2*fuel+5,0);int origin=fuel+2,last_lo=0,last_hi=0;
    long long rows=0,blank_a=0,blank_b=0,undefined=0,budget=0,steps=0;
    string machine;auto start=chrono::steady_clock::now();
    while(getline(input,machine)) {
      auto tm=table(machine);++rows;
      fill(tape.begin()+origin+last_lo,tape.begin()+origin+last_hi+1,0);
      int pos=0,q=0,nonzero=0,lo=0,hi=0;bool done=false;
      for(int t=0;t<fuel;++t) {
        int before=tape[origin+pos],tr=tm[4*q+before];
        if(tr==16) {++undefined;done=true;break;}
        int after=tr/4;nonzero+=(after!=0)-(before!=0);tape[origin+pos]=after;
        q=tr%2;pos+=(tr&2)?1:-1;lo=min(lo,pos);hi=max(hi,pos);++steps;
        if(nonzero==0) {
          if(q)++blank_b;else ++blank_a;
          output<<machine<<'\t'<<t+1<<'\t'<<(q?'B':'A')<<'\t'<<pos<<'\n';
          done=true;break;
        }
      }
      if(!done)++budget;
      last_lo=lo;last_hi=hi;
    }
    cout<<"{\"families\":"<<rows<<",\"blank_a\":"<<blank_a<<",\"blank_b\":"<<blank_b
        <<",\"undefined\":"<<undefined<<",\"budget\":"<<budget<<",\"steps\":"<<steps
        <<",\"seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"}\n";
  }catch(const exception& e){cerr<<e.what()<<'\n';return 2;}
}
