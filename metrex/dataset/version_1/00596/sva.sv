// SVA for GrayCounter
module GrayCounter_sva #(parameter COUNTER_WIDTH = 4)
(
  input  wire                         clk,
  input  wire                         rst,
  input  wire                         en,
  input  wire [COUNTER_WIDTH-1:0]     gray_count_out,
  input  wire [COUNTER_WIDTH-1:0]     binary_count
);

  localparam int W = COUNTER_WIDTH;

  // Optional static sanity
  initial begin
    assert (W >= 2)
      else $error("GrayCounter_sva: COUNTER_WIDTH must be >= 2");
  end

  function automatic [W-1:0] gray(input [W-1:0] b);
    return {b[W-1], b[W-2:0] ^ b[W-1:1]};
  endfunction

  default clocking cb @(posedge clk); endclocking

  // No X/Z on key signals
  a_no_xz: assert property ( !$isunknown({rst,en,gray_count_out,binary_count}) );

  // Synchronous reset behavior
  a_reset_vals: assert property ( rst |=> (binary_count == {{W-1{1'b0}},1'b1}) && (gray_count_out == {W{1'b0}}) );

  // Hold when disabled
  a_hold_when_disabled: assert property ( (!rst && !en) |=> $stable(binary_count) && $stable(gray_count_out) );

  // Increment and gray mapping (uses previous binary_count)
  a_inc_and_map: assert property (
    (!rst && en) |=> (binary_count == $past(binary_count)+1) &&
                     (gray_count_out == gray($past(binary_count)))
  );

  // First enable after being disabled: gray holds one cycle (due to RHS using $past(binary_count))
  a_en_rise_gray_holds: assert property (
    (!rst && en && !$past(en) && !$past(rst)) |-> (gray_count_out == $past(gray_count_out))
  );

  // Consecutive enables: gray must change by exactly one bit
  a_gray_one_bit_change: assert property (
    (!rst && en && $past(en) && !$past(rst)) |-> $onehot(gray_count_out ^ $past(gray_count_out))
  );

  // Optional: general mapping holds whenever not in or just after reset
  a_map_general: assert property (
    (!rst && !$past(rst)) |-> (gray_count_out == gray($past(binary_count)))
  );

  // Coverage
  c_reset:                cover property (rst);
  c_first_en_after_reset: cover property (!rst && !$past(rst) && en && !$past(en));
  c_consecutive_en:       cover property (!rst && en && $past(en) && !$past(rst));
  c_hold:                 cover property (!rst && !en && !$past(en) && !$past(rst));
  c_rollover:             cover property (!rst && en && ($past(binary_count) == {W{1'b1}}));

endmodule

// Bind into DUT
bind GrayCounter GrayCounter_sva #(.COUNTER_WIDTH(COUNTER_WIDTH)) u_graycounter_sva (
  .clk(clk),
  .rst(rst),
  .en(en),
  .gray_count_out(gray_count_out),
  .binary_count(binary_count)
)