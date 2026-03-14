module top_module_sva (
    input logic clk,
    input logic reset,        // Synchronous active-high reset
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic select,
    input logic [7:0] q
);
    // 9-bit adder helper (matches adder module behavior)
    function automatic logic [8:0] f_add9(input logic [7:0] a, input logic [7:0] b, input logic c);
        f_add9 = {1'b0, a} + {1'b0, b} + {8'b0, c};
    endfunction

    // Reference model for internal state behavior
    logic [7:0] m_q1, m_q2;
    logic m_cin1, m_cin2;

    always_ff @(posedge clk) begin
        if (reset) begin
            m_q1  <= '0;
            m_q2  <= '0;
            m_cin1 <= 1'b0;
            m_cin2 <= 1'b0;
        end else begin
            if (select) begin
                m_q1  <= d1;
                m_cin1 <= 1'b0;
                m_q2  <= f_add9(d1, m_q1, m_cin1)[7:0];
                m_cin2 <= f_add9(d1, m_q1, m_cin1)[8];
            end else begin
                m_q2  <= d2;
                m_cin2 <= 1'b0;
                m_q1  <= f_add9(d2, m_q2, m_cin2)[7:0];
                m_cin1 <= f_add9(d2, m_q2, m_cin2)[8];
            end
        end
    end

    ///// Assertions /////
    // Q must be 0 during synchronous active-high reset.
    check_q_zero_during_reset: assert property (
        @(posedge clk) reset |-> (q == 8'h00)
    );

    // When select=1, q equals d1 + m_q1 + m_cin1 (low 8 bits).
    check_q_model_sel1: assert property (
        @(posedge clk) disable iff (reset) select |-> (q == f_add9(d1, m_q1, m_cin1)[7:0])
    );

    // When select=0, q equals d2 + m_q2 + m_cin2 (low 8 bits).
    check_q_model_sel0: assert property (
        @(posedge clk) disable iff (reset) !select |-> (q == f_add9(d2, m_q2, m_cin2)[7:0])
    );

    // First cycle after reset deasserts, q equals selected input (internal state zeros).
    check_q_after_reset_release: assert property (
        @(posedge clk) disable iff (reset) $fell(reset) |-> (q == (select ? d1 : d2))
    );

    // With select=1 for two cycles, q equals d1 + $past(d1) (no carry-in).
    check_two_cycle_sel1_addition: assert property (
        @(posedge clk) disable iff (reset)
            (select && $past(select) && !$past(reset)) |-> (q == f_add9(d1, $past(d1), 1'b0)[7:0])
    );

    // With select=0 for two cycles, q equals d2 + $past(d2) (no carry-in).
    check_two_cycle_sel0_addition: assert property (
        @(posedge clk) disable iff (reset)
            (!select && !$past(select) && !$past(reset)) |-> (q == f_add9(d2, $past(d2), 1'b0)[7:0])
    );
endmodule