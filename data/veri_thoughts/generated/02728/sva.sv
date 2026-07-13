module mem_encryption_sva (
    input logic         clk,
    input logic         reset,
    input logic [31:0]  data_in,
    input logic [31:0]  key,
    input logic [31:0]  data_out,
    input logic [31:0]  internal_state
);
    // Clock: clk (posedge). Reset: reset (active-high synchronous).
    // Sequential: registers internal_state and data_out update on posedge clk.
    // Function: reset clears regs; key==0 -> data_out=data_in, hold internal_state; else -> internal_state=data_in^key, data_out=$past(internal_state)^key.

    // On reset, both internal_state and data_out are driven to 0.
    reset_clears_regs: assert property (
        @(posedge clk) reset |-> (internal_state == 32'h0) && (data_out == 32'h0)
    );

    // When key is zero, data_out passes through data_in.
    key_zero_passthrough: assert property (
        @(posedge clk) disable iff (reset) (key == 32'h0) |-> (data_out == data_in)
    );

    // When key is zero, internal_state holds its previous value.
    hold_internal_state_when_key_zero: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (key == 32'h0)) |-> (internal_state == $past(internal_state))
    );

    // When key is nonzero, internal_state updates to data_in ^ key in the same cycle.
    update_internal_state_when_key_nonzero: assert property (
        @(posedge clk) disable iff (reset) (key != 32'h0) |-> (internal_state == (data_in ^ key))
    );

    // When key is nonzero, data_out uses previous internal_state XOR current key.
    data_out_uses_prev_internal_state_when_key_nonzero: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (key != 32'h0)) |-> (data_out == ($past(internal_state) ^ key))
    );

    // First cycle after reset with nonzero key: data_out equals key (prev internal_state was 0).
    first_nonzero_key_after_reset_outputs_key: assert property (
        @(posedge clk) disable iff (reset) ($past(reset) && (key != 32'h0)) |-> (data_out == key)
    );

    // If previous cycle had nonzero key and current key is zero, internal_state equals previous data_in ^ previous key.
    internal_state_matches_prev_calc_on_key_drop_to_zero: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (key == 32'h0) && ($past(key) != 32'h0)) |-> (internal_state == ($past(data_in) ^ $past(key)))
    );

    // With nonzero keys in two consecutive cycles, data_out equals (prev data_in ^ prev key) ^ current key.
    data_out_two_cycle_relation_when_key_nonzero_consecutive: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && !$past(reset,2) && (key != 32'h0) && ($past(key) != 32'h0)) |-> (data_out == (($past(data_in) ^ $past(key)) ^ key))
    );

endmodule