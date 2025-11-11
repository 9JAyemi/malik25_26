// Bindable SVA checker for mux4
module mux4_sva (
  input logic                 clk,
  input logic [3:0]           in0,
  input logic [3:0]           in1,
  input logic [3:0]           in2,
  input logic [3:0]           in3,
  input logic [1:0]           sel,
  input logic                 en,
  input logic [3:0]           out
);
  default clocking cb @(posedge clk); endclocking

  // Core functional correctness (when controls are known)
  property p_mux_func;
    !$isunknown({en,sel}) |->
      out == (en ? (sel==2'b00 ? in0 :
                    sel==2'b01 ? in1 :
                    sel==2'b10 ? in2 : in3)
                 : 4'b0);
  endproperty
  assert property (p_mux_func);

  // Disabled drives zero
  assert property (!en |-> out == 4'b0);

  // No X on output when controls are known
  assert property (!$isunknown({en,sel}) |-> !$isunknown(out));

  // Functional coverage of all selections and disable
  cover property (!en);
  cover property (en && sel==2'b00 && out==in0);
  cover property (en && sel==2'b01 && out==in1);
  cover property (en && sel==2'b10 && out==in2);
  cover property (en && sel==2'b11 && out==in3);
endmodule

// Example bind (adjust instance path and clock as needed):
// bind mux4 mux4_sva u_mux4_sva(.clk(clk), .in0(in0), .in1(in1), .in2(in2), .in3(in3), .sel(sel), .en(en), .out(out));