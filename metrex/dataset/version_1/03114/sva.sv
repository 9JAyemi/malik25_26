// SVA for adder_4bit
module adder_4bit_sva (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic       cin,
  input  logic [3:0] sum,
  input  logic       cout,
  input  logic [3:0] carry
);

  // Functional correctness (sample after combinational settle)
  a_add_correct: assert property (@(a or b or cin)
                                  ##0 {cout,sum} == ({1'b0,a} + {1'b0,b} + cin));

  // Bit-level sum checks
  a_sum0: assert property (@(a or b or cin) ##0 sum[0] == (a[0] ^ b[0] ^ cin));
  a_sum1: assert property (@(a or b or cin) ##0 sum[1] == (a[1] ^ b[1] ^ carry[1]));
  a_sum2: assert property (@(a or b or cin) ##0 sum[2] == (a[2] ^ b[2] ^ carry[2]));
  a_sum3: assert property (@(a or b or cin) ##0 sum[3] == (a[3] ^ b[3] ^ carry[3]));

  // Carry chain correctness (including c0)
  a_c0: assert property (@(a or b or cin) ##0 carry[0] == cin);
  a_c1: assert property (@(a or b or cin) ##0 carry[1] == ((a[0] & b[0]) | (a[0] & cin)      | (b[0] & cin)));
  a_c2: assert property (@(a or b or cin) ##0 carry[2] == ((a[1] & b[1]) | (a[1] & carry[1]) | (b[1] & carry[1])));
  a_c3: assert property (@(a or b or cin) ##0 carry[3] == ((a[2] & b[2]) | (a[2] & carry[2]) | (b[2] & carry[2])));

  // True final carry-out of MSB (will catch any missing MSB carry generation)
  a_cout_true: assert property (@(a or b or cin) ##0
                                cout == ((a[3] & b[3]) | (a[3] & carry[3]) | (b[3] & carry[3])));

  // No X/Z on outputs when inputs are 0/1
  a_no_x: assert property (@(a or b or cin)
                           !$isunknown({a,b,cin}) |-> ##0 !$isunknown({sum,cout,carry}));

  // Minimal functional coverage
  c_zero:       cover property (@(a or b or cin) ##0 (a==4'h0 && b==4'h0 && cin==1'b0));
  c_overflow:   cover property (@(a or b or cin) ##0 (({1'b0,a}+{1'b0,b}+cin) > 5'd15));
  c_propagate:  cover property (@(a or b or cin) ##0 ((a ^ b) == 4'hF && cin==1'b1)); // full ripple
  c_max_inputs: cover property (@(a or b or cin) ##0 (a==4'hF && b==4'hF && cin==1'b1));

endmodule

bind adder_4bit adder_4bit_sva sva (.*);