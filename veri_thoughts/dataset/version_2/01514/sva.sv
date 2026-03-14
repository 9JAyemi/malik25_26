module moore_state_machine_sva #(
    parameter int k = 4,
    parameter int n = 2
) (
    input  logic              clk,
    input  logic              rst,
    input  logic [n-1:0]      out,
    input  logic [k-1:0]      state_reg,
    input  logic [k-1:0]      next_state
);
    // Mirror DUT encodings
    localparam logic [k-1:0] STATE_A = 'd0;
    localparam logic [k-1:0] STATE_B = 'd1;
    localparam logic [k-1:0] STATE_C = 'd2;
    localparam logic [k-1:0] STATE_D = 'd3;

    localparam logic [n-1:0] OUT_A   = 'd0;
    localparam logic [n-1:0] OUT_B   = 'd1;
    localparam logic [n-1:0] OUT_C   = 'd2;
    localparam logic [n-1:0] OUT_D   = 'd3;

    ///// Reset behavior /////
    // While reset is asserted, state_reg is forced to STATE_A.
    reset_state_is_A: assert property (
        @(posedge clk) rst |-> (state_reg == STATE_A)
    );
    // While reset is asserted, out is forced to OUT_A.
    reset_out_is_A: assert property (
        @(posedge clk) rst |-> (out == OUT_A)
    );

    ///// Output decode (Moore) /////
    // In non-reset, STATE_A maps to OUT_A.
    map_state_A_to_out_A: assert property (
        @(posedge clk) disable iff (rst) (state_reg == STATE_A) |-> (out == OUT_A)
    );
    // In non-reset, STATE_B maps to OUT_B.
    map_state_B_to_out_B: assert property (
        @(posedge clk) disable iff (rst) (state_reg == STATE_B) |-> (out == OUT_B)
    );
    // In non-reset, STATE_C maps to OUT_C.
    map_state_C_to_out_C: assert property (
        @(posedge clk) disable iff (rst) (state_reg == STATE_C) |-> (out == OUT_C)
    );
    // In non-reset, STATE_D maps to OUT_D.
    map_state_D_to_out_D: assert property (
        @(posedge clk) disable iff (rst) (state_reg == STATE_D) |-> (out == OUT_D)
    );

    ///// Next-state combinational logic /////
    // In non-reset, next_state for STATE_A is STATE_B.
    next_logic_A_to_B: assert property (
        @(posedge clk) disable iff (rst) (state_reg == STATE_A) |-> (next_state == STATE_B)
    );
    // In non-reset, next_state for STATE_B is STATE_C.
    next_logic_B_to_C: assert property (
        @(posedge clk) disable iff (rst) (state_reg == STATE_B) |-> (next_state == STATE_C)
    );
    // In non-reset, next_state for STATE_C is STATE_D.
    next_logic_C_to_D: assert property (
        @(posedge clk) disable iff (rst) (state_reg == STATE_C) |-> (next_state == STATE_D)
    );
    // In non-reset, next_state for STATE_D is STATE_A.
    next_logic_D_to_A: assert property (
        @(posedge clk) disable iff (rst) (state_reg == STATE_D) |-> (next_state == STATE_A)
    );

    ///// State register update /////
    // When not in reset in consecutive cycles, state_reg captures previous next_state.
    state_updates_from_prev_next: assert property (
        @(posedge clk) disable iff (rst) ($past(rst) === 1'b0) |-> (state_reg == $past(next_state))
    );

    ///// Output sequencing /////
    // On reset deassertion, the next cycle's output is OUT_B.
    out_after_reset_deassert_is_B: assert property (
        @(posedge clk) $fell(rst) |=> (out == OUT_B)
    );
    // In non-reset, OUT_A transitions to OUT_B on the next cycle.
    out_seq_A_to_B: assert property (
        @(posedge clk) disable iff (rst) (out == OUT_A) |=> (out == OUT_B)
    );
    // In non-reset, OUT_B transitions to OUT_C on the next cycle.
    out_seq_B_to_C: assert property (
        @(posedge clk) disable iff (rst) (out == OUT_B) |=> (out == OUT_C)
    );
    // In non-reset, OUT_C transitions to OUT_D on the next cycle.
    out_seq_C_to_D: assert property (
        @(posedge clk) disable iff (rst) (out == OUT_C) |=> (out == OUT_D)
    );
    // In non-reset, OUT_D transitions to OUT_A on the next cycle.
    out_seq_D_to_A: assert property (
        @(posedge clk) disable iff (rst) (out == OUT_D) |=> (out == OUT_A)
    );

endmodule