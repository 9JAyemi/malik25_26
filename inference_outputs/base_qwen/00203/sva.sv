module BusHold_sva (
  input logic [7:0] in,
  input logic clk,
  input logic rst,
  output logic [7:0] out
);
    ///// Bus hold logic /////
    // The output should hold the value of the input on the rising edge of the clock.
    hold_value: assert property (
        @(posedge clk) disable iff (!rst) out == in
    );
    // The register should be reset to 0 on the rising edge of the reset.
    reset_value: assert property (
        @(posedge clk) disable iff (!rst) hold == 8'b0
    );
endmodule