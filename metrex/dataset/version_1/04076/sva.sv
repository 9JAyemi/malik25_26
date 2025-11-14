// SVA for binary_counter
module binary_counter_sva (
  input logic       clk,
  input logic       rst,
  input logic [3:0] count
);
  default clocking cb @(posedge clk); endclocking

  // Guard for $past on first cycle
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // No X/Z on critical signals
  a_no_x: assert property (!$isunknown({rst,count}));

  // Synchronous reset drives zero every cycle it's asserted
  a_rst_zero: assert property (rst |-> count == 4'h0);

  // Next-state relation when running (no reset in current and previous cycle)
  a_next_state: assert property (
    past_valid && !rst && $past(!rst) |->
      ( ($past(count)==4'hF && count==4'h0) ||
        ($past(count)!=4'hF && count==$past(count)+1) )
  );

  // Zero can only be reached by reset or wrap from 15
  a_zero_origin: assert property (
    past_valid && !rst && count==4'h0 |-> ($past(rst) || $past(count)==4'hF)
  );

  // Functional coverage (states, increments, wrap) when not in reset
  covergroup cg_cnt @(posedge clk iff !rst);
    coverpoint count {
      bins all_vals[] = {[0:15]};
      bins inc = ( [0:14] => [1:15] );
      bins wrap = ( 15 => 0 );
    }
  endgroup
  cg_cnt cg = new;

  // Event coverage
  c_wrap: cover property (!rst && $past(!rst) && $past(count)==4'hF && count==4'h0);
  c_rst_rise: cover property ($rose(rst));
  c_rst_fall: cover property ($fell(rst));
endmodule

// Bind into the DUT
bind binary_counter binary_counter_sva u_binary_counter_sva (.clk(clk), .rst(rst), .count(count));