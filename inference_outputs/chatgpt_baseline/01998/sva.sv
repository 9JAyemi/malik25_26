module priority_encoder_sva #(
  parameter int n = 4,
  parameter int m = 2
) (
  input  logic              clk,   // external sampling clock for assertions
  input  logic [n-1:0]      in,
  input  logic [m-1:0]      out
);
  // Clocks/resets: none in RTL; assertions sampled on clk. Logic: purely combinational always @(*).
  // Function: exact mappings 1110->00, 1101->01, 1011->10, 0111->11; all other inputs -> 00.

  generate
    if ((n == 4) && (m == 2)) begin : gen_sva
      // When in==4'b1110, out must be 2'b00.
      map_in_1110_to_out_00: assert property (
        @(posedge clk) (in === 4'b1110) |-> (out == 2'b00)
      );
      // When in==4'b1101, out must be 2'b01.
      map_in_1101_to_out_01: assert property (
        @(posedge clk) (in === 4'b1101) |-> (out == 2'b01)
      );
      // When in==4'b1011, out must be 2'b10.
      map_in_1011_to_out_10: assert property (
        @(posedge clk) (in === 4'b1011) |-> (out == 2'b10)
      );
      // When in==4'b0111, out must be 2'b11.
      map_in_0111_to_out_11: assert property (
        @(posedge clk) (in === 4'b0111) |-> (out == 2'b11)
      );
      // For any input not matching the four patterns, out must be 2'b00 (default case).
      default_for_unmatched_inputs: assert property (
        @(posedge clk) (in !== 4'b1110) && (in !== 4'b1101) && (in !== 4'b1011) && (in !== 4'b0111) |-> (out == 2'b00)
      );
      // out==2'b01 only occurs for in==4'b1101.
      only_out_01_on_1101: assert property (
        @(posedge clk) (out == 2'b01) |-> (in === 4'b1101)
      );
      // out==2'b10 only occurs for in==4'b1011.
      only_out_10_on_1011: assert property (
        @(posedge clk) (out == 2'b10) |-> (in === 4'b1011)
      );
      // out==2'b11 only occurs for in==4'b0111.
      only_out_11_on_0111: assert property (
        @(posedge clk) (out == 2'b11) |-> (in === 4'b0111)
      );
    end
  endgenerate
endmodule