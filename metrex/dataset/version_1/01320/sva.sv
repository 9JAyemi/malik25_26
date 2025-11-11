// SVA checker for adder. Bind into DUT; no TB changes required.
module adder_sva;
  // Bound inside adder; can see a,b,cin,sum,cout,c1,c2,c3
  default clocking cb @($global_clock); endclocking

  // Functional correctness (5-bit result)
  ap_func: assert property (1'b1 |-> ##0 {cout,sum} == ({1'b0,a}+{1'b0,b}+cin))
    else $error("adder mismatch: a=%0h b=%0h cin=%0b sum=%0h cout=%0b", a,b,cin,sum,cout);

  // No X/Z on outputs when inputs are known
  ap_no_x: assert property (!($isunknown({a,b,cin})) |-> ##0 !($isunknown({sum,cout})))
    else $error("adder produced X/Z: a=%0h b=%0h cin=%0b sum=%0h cout=%0b", a,b,cin,sum,cout);

  // Stage-by-stage full-adder equations (internal ripple carries)
  ap_s0: assert property (!($isunknown({a[0],b[0],cin})) |-> ##0
                          (sum[0] == (a[0]^b[0]^cin)) &&
                          (c1     == ((a[0]&b[0]) | (a[0]&cin) | (b[0]&cin))));
  ap_s1: assert property (!($isunknown({a[1],b[1],c1})) |-> ##0
                          (sum[1] == (a[1]^b[1]^c1)) &&
                          (c2     == ((a[1]&b[1]) | (a[1]&c1) | (b[1]&c1))));
  ap_s2: assert property (!($isunknown({a[2],b[2],c2})) |-> ##0
                          (sum[2] == (a[2]^b[2]^c2)) &&
                          (c3     == ((a[2]&b[2]) | (a[2]&c2) | (b[2]&c2))));
  ap_s3: assert property (!($isunknown({a[3],b[3],c3})) |-> ##0
                          (sum[3] == (a[3]^b[3]^c3)) &&
                          (cout   == ((a[3]&b[3]) | (a[3]&c3) | (b[3]&c3))));

  // Sanity: 5-bit range of result
  ap_range: assert property (1'b1 |-> ##0 {cout,sum} inside {[5'd0:5'd31]});

  // Coverage
  cp_min:   cover property (##0 ({1'b0,a}+{1'b0,b}+cin) == 5'd0);   // 0+0+0
  cp_max:   cover property (##0 ({1'b0,a}+{1'b0,b}+cin) == 5'd31);  // 15+15+1
  // Full propagate chain with cin=1 → cout=1, sum=0
  cp_pall:  cover property (((a^b)==4'hF) && (cin==1) ##0 (cout==1) && (sum==4'h0));
  // Generate at each stage observed on next carry
  cp_gen0:  cover property ((a[0]&b[0]) ##0 c1);
  cp_gen1:  cover property ((a[1]&b[1]) ##0 c2);
  cp_gen2:  cover property ((a[2]&b[2]) ##0 c3);
  cp_gen3:  cover property ((a[3]&b[3]) ##0 cout);
endmodule

bind adder adder_sva adder_sva_i();