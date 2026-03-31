```systemverilog
module freq_divider_sva (
  input logic clk_in,
  output logic clk_out
);
  parameter n = 2; // division factor
  
  reg [31:0] count;
  
  always @(posedge clk_in) begin
    if (count == n-1) begin
      clk_out <= ~clk_out;
      count <= 0;
    end else begin
      count <= count + 1;
    end
  end
  
  ///// Frequency Divider Behavior /////
  // clk_out toggles every n clock cycles of clk_in.
  toggle_clk_out: assert property (
    @(posedge clk_in) disable iff (!clk_in) (count == n-1) |-> $rose(clk_out)
  );
  // count increments on every positive edge of clk_in.
  count_increments: assert property (
    @(posedge clk_in) disable iff (!clk_in) count |-> count + 1
  );
  // count resets to 0 when it reaches n-1.
  count_resets: assert property (
    @(posedge clk_in) disable iff (!clk_in) (count == n-1) |-> count == 0
  );
  // clk_out is always either 0 or 1.
  clk_out_valid: assert property (
    @(posedge clk_in) disable iff (!clk_in) (clk_out == 1'b0) || (clk_out == 1'b1)
  );
  // count is always within the range of 0 to n-1.
  count_range: assert property (
    @(posedge clk_in) disable iff (!clk_in) (count >= 0) && (count <= n-1)
  );
  // clk_out toggles exactly once per n clock cycles of clk_in.
  toggle_once_per_n: assert property (
    @(posedge clk_in) disable iff (!clk_in) (count == n-1) |-> $rose(clk_out) && $fell(clk_out)
  );
  // count increments by 1 on every positive edge of clk_in.
  count_increment_by_1: assert property (
    @(posedge clk_in) disable iff (!clk_in) count |-> count + 1
  );
  // count resets to 0 when it reaches n-1.
  count_reset_to_0: assert property (
    @(posedge clk_in) disable iff (!clk_in) (count == n-1) |-> count == 0
  );
  // clk_out is always either 0 or 1.
  clk_out_is_valid: assert property (
    @(posedge clk_in) disable iff (!clk_in) (clk_out == 1'b0) || (clk_out == 1'b1)
  );
  // count is always within the range of 0 to n-1.
  count_is_in_range: assert property (
    @(posedge clk_in) disable iff (!clk_in) (count >= 0) && (count <= n-1)
  );
endmodule
```