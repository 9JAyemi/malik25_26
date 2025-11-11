// SVA checker for top_module (8:1 mux)
`ifndef SYNTHESIS
module top_module_sva (
  input logic [2:0] sel,
  input logic [3:0] data0,
  input logic [3:0] data1,
  input logic [3:0] data2,
  input logic [3:0] data3,
  input logic [3:0] data4,
  input logic [3:0] data5,
  input logic [3:0] data6,
  input logic [3:0] data7,
  input logic [3:0] out
);

  // Functional correctness (4-state equality to catch X/Z mismatches)
  property p_mux_func;
    @(*) out === ((sel==3'd0) ? data0 :
                  (sel==3'd1) ? data1 :
                  (sel==3'd2) ? data2 :
                  (sel==3'd3) ? data3 :
                  (sel==3'd4) ? data4 :
                  (sel==3'd5) ? data5 :
                  (sel==3'd6) ? data6 : data7);
  endproperty
  assert property (p_mux_func);

  // Out must be known if select is known and the selected input is known
  property p_known_out_when_known_in;
    @(*) (!$isunknown(sel) &&
          !$isunknown((sel==3'd0) ? data0 :
                      (sel==3'd1) ? data1 :
                      (sel==3'd2) ? data2 :
                      (sel==3'd3) ? data3 :
                      (sel==3'd4) ? data4 :
                      (sel==3'd5) ? data5 :
                      (sel==3'd6) ? data6 : data7))
         |-> !$isunknown(out);
  endproperty
  assert property (p_known_out_when_known_in);

  // Optional: flag unknown select (often indicates testbench/init issue)
  assert property (@(*) !$isunknown(sel))
    else $error("top_module: sel has X/Z");

  // Coverage: observe every select value with correct pass-through
  cover property (@(*) sel==3'd0 && out===data0);
  cover property (@(*) sel==3'd1 && out===data1);
  cover property (@(*) sel==3'd2 && out===data2);
  cover property (@(*) sel==3'd3 && out===data3);
  cover property (@(*) sel==3'd4 && out===data4);
  cover property (@(*) sel==3'd5 && out===data5);
  cover property (@(*) sel==3'd6 && out===data6);
  cover property (@(*) sel==3'd7 && out===data7);

endmodule

// Bind into the DUT
bind top_module top_module_sva u_top_module_sva (.*);
`endif