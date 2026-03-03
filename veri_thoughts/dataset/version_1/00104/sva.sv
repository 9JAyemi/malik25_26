// SVA checker for mux_4to2. Bind this to the DUT and provide a sampling clock.
// Example:
// bind mux_4to2 mux_4to2_sva u_mux_4to2_sva (.* , .clk(tb_clk));

module mux_4to2_sva(
  input logic         clk,
  input logic         in0,
  input logic         in1,
  input logic         in2,
  input logic         in3,
  input logic [1:0]   sel,
  input logic [1:0]   out
);

  default clocking @(posedge clk); endclocking

  // Expected MSB when sel is 2-state
  function automatic logic exp_msb_knownsel(
    input logic in0, in1, in2, in3,
    input logic [1:0] sel
  );
    unique case (sel)
      2'b00: exp_msb_knownsel = in0;
      2'b01: exp_msb_knownsel = in1;
      2'b10: exp_msb_knownsel = in2;
      2'b11: exp_msb_knownsel = in3;
    endcase
  endfunction

  // Disallow X/Z on select (avoids unintended latch behavior)
  assert property (!$isunknown(sel))
    else $error("mux_4to2: sel has X/Z");

  // Functional correctness when select is known
  assert property ( !$isunknown(sel)
                    |-> (out === {exp_msb_knownsel(in0,in1,in2,in3,sel), 1'b0}) )
    else $error("mux_4to2: functional mismatch");

  // Basic functional coverage: observe each select value
  cover property (sel == 2'b00);
  cover property (sel == 2'b01);
  cover property (sel == 2'b10);
  cover property (sel == 2'b11);

  // Cover data steering for each leg when input=1 (MSB=1, LSB=0)
  cover property (sel == 2'b00 && in0 == 1'b1 && out == 2'b10);
  cover property (sel == 2'b01 && in1 == 1'b1 && out == 2'b10);
  cover property (sel == 2'b10 && in2 == 1'b1 && out == 2'b10);
  cover property (sel == 2'b11 && in3 == 1'b1 && out == 2'b10);

endmodule