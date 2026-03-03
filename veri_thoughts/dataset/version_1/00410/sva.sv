// SVA for up_down_counter
module up_down_counter_sva (
  input logic        clk,
  input logic        load,
  input logic        up_down,
  input logic [2:0]  out
);
  localparam int WIDTH = $bits(out);
  typedef logic [WIDTH-1:0] T;

  default clocking cb @(posedge clk); endclocking

  logic past_valid; initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Sanity/X checks
  ap_load_known:       assert property ( !$isunknown(load) );
  ap_ud_known_when_used: assert property ( load || !$isunknown(up_down) );
  ap_out_known:        assert property ( past_valid |-> !$isunknown(out) );

  // Functional next-state (modulo-2**WIDTH)
  ap_next_state: assert property (
    past_valid |=> out ==
      ( $past(load) ? '0
        : ($past(up_down) ? T'($past(out)+1) : T'($past(out)-1)) )
  );

  // Coverage: each branch and both wraps
  cv_load:      cover property ( past_valid && load |=> out == '0 );
  cv_inc:       cover property ( past_valid && !load && up_down |=> out == T'($past(out)+1) );
  cv_dec:       cover property ( past_valid && !load && !up_down |=> out == T'($past(out)-1) );
  cv_wrap_up:   cover property ( past_valid && !load && up_down && (out == {WIDTH{1'b1}}) |=> out == '0 );
  cv_wrap_down: cover property ( past_valid && !load && !up_down && (out == '0)             |=> out == {WIDTH{1'b1}} );
endmodule

// Bind into DUT
bind up_down_counter up_down_counter_sva sva(.clk(clk), .load(load), .up_down(up_down), .out(out));