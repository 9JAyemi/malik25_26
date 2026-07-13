module debouncer_sva (
    input logic        clk,
    input logic        reset,
    input logic        sw,
    input logic        db,
    input logic [18:0] q_reg,
    input logic [18:0] q_next,
    input logic        m_tick,
    input logic [2:0]  state_reg,
    input logic [2:0]  state_next
);

    localparam [2:0]
        zero    = 3'b000,
        wait1_1 = 3'b001,
        wait1_2 = 3'b010,
        wait1_3 = 3'b011,
        one     = 3'b100,
        wait0_1 = 3'b101,
        wait0_2 = 3'b110,
        wait0_3 = 3'b111;

    // A sampled reset must leave the FSM in zero on the next clock.
    check_reset_state_zero: assert property (
        @(posedge clk) reset |=> (state_reg == zero)
    );

    // A sampled reset must leave the debounced output low on the next clock.
    check_reset_db_low: assert property (
        @(posedge clk) reset |=> (db == 1'b0)
    );

    // q_next is always q_reg plus one.
    check_counter_next_increment: assert property (
        @(posedge clk) disable iff (reset)
        (q_next == (q_reg + 19'd1))
    );

    // m_tick is asserted exactly when q_reg is zero.
    check_mtick_decode: assert property (
        @(posedge clk) disable iff (reset)
        (m_tick == (q_reg == 19'd0))
    );

    // The free-running counter increments every clock.
    check_counter_register_update: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (q_reg == ($past(q_reg) + 19'd1))
    );

    // The FSM register loads state_next when reset is not active.
    check_state_register_update: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (state_reg == $past(state_next))
    );

    // zero and wait1 states must drive db low.
    check_db_low_state_decode: assert property (
        @(posedge clk) disable iff (reset)
        ((state_reg == zero) || (state_reg == wait1_1) || (state_reg == wait1_2) || (state_reg == wait1_3))
        |-> (db == 1'b0)
    );

    // one and wait0 states must drive db high.
    check_db_high_state_decode: assert property (
        @(posedge clk) disable iff (reset)
        ((state_reg == one) || (state_reg == wait0_1) || (state_reg == wait0_2) || (state_reg == wait0_3))
        |-> (db == 1'b1)
    );

    // zero either holds or starts the high-debounce sequence.
    check_zero_transitions: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == zero)
        |-> ((!sw && (state_next == zero)) ||
             ( sw && (state_next == wait1_1)))
    );

    // wait1_1 either cancels, holds, or advances on m_tick.
    check_wait1_1_transitions: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == wait1_1)
        |-> ((!sw && (state_next == zero)) ||
             ( sw && !m_tick && (state_next == wait1_1)) ||
             ( sw &&  m_tick && (state_next == wait1_2)))
    );

    // wait1_2 either cancels, holds, or advances on m_tick.
    check_wait1_2_transitions: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == wait1_2)
        |-> ((!sw && (state_next == zero)) ||
             ( sw && !m_tick && (state_next == wait1_2)) ||
             ( sw &&  m_tick && (state_next == wait1_3)))
    );

    // wait1_3 either cancels, holds, or advances to one on m_tick.
    check_wait1_3_transitions: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == wait1_3)
        |-> ((!sw && (state_next == zero)) ||
             ( sw && !m_tick && (state_next == wait1_3)) ||
             ( sw &&  m_tick && (state_next == one)))
    );

    // one either holds or starts the low-debounce sequence.
    check_one_transitions: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == one)
        |-> (( sw && (state_next == one)) ||
             (!sw && (state_next == wait0_1)))
    );

    // wait0_1 either returns to one, holds, or advances on m_tick.
    check_wait0_1_transitions: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == wait0_1)
        |-> (( sw && (state_next == one)) ||
             (!sw && !m_tick && (state_next == wait0_1)) ||
             (!sw &&  m_tick && (state_next == wait0_2)))
    );

    // wait0_2 either returns to one, holds, or advances on m_tick.
    check_wait0_2_transitions: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == wait0_2)
        |-> (( sw && (state_next == one)) ||
             (!sw && !m_tick && (state_next == wait0_2)) ||
             (!sw &&  m_tick && (state_next == wait0_3)))
    );

    // wait0_3 either returns to one, holds, or advances to zero on m_tick.
    check_wait0_3_transitions: assert property (
        @(posedge clk) disable iff (reset)
        (state_reg == wait0_3)
        |-> (( sw && (state_next == one)) ||
             (!sw && !m_tick && (state_next == wait0_3)) ||
             (!sw &&  m_tick && (state_next == zero)))
    );

endmodule

bind debouncer debouncer_sva debouncer_sva_i (
    .clk(clk),
    .reset(reset),
    .sw(sw),
    .db(db),
    .q_reg(q_reg),
    .q_next(q_next),
    .m_tick(m_tick),
    .state_reg(state_reg),
    .state_next(state_next)
);