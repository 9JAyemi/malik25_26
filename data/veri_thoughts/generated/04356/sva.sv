module even_parity_checker_assertions (
    input logic D0,
    input logic D1,
    input logic D2,
    input logic D3,
    input logic RST,
    input logic ECLK,
    input logic DQSW,
    input logic Q,
    input logic [3:0] data_reg
);

    // After reset is released, Q reflects the reset value.
    check_reset_state_after_release_q: assert property (
        @(posedge ECLK) disable iff (RST)
        !$initstate && $past(RST) |-> (Q == 1'b0)
    );

    // After reset is released, data_reg reflects the reset value.
    check_reset_state_after_release_data_reg: assert property (
        @(posedge ECLK) disable iff (RST)
        !$initstate && $past(RST) |-> (data_reg == 4'b0000)
    );

    // In shift mode, Q holds its previous value.
    check_shift_mode_holds_q: assert property (
        @(posedge ECLK) disable iff (RST)
        !DQSW |=> (Q == $past(Q))
    );

    // In shift mode, data_reg shifts and captures D3 into bit 0.
    check_shift_mode_updates_data_reg: assert property (
        @(posedge ECLK) disable iff (RST)
        !DQSW |=> (data_reg == { $past(data_reg[2:0]), $past(D3) })
    );

    // In load mode, Q becomes the even parity of the previous data_reg.
    check_load_mode_updates_q: assert property (
        @(posedge ECLK) disable iff (RST)
        DQSW |=> (Q == ~^$past(data_reg))
    );

    // In load mode, data_reg captures D3:D0 in order.
    check_load_mode_updates_data_reg: assert property (
        @(posedge ECLK) disable iff (RST)
        DQSW |=> (data_reg == { $past(D3), $past(D2), $past(D1), $past(D0) })
    );

    // Q can only change after a reset cycle or a load-mode cycle.
    check_q_changes_only_on_reset_or_load: assert property (
        @(posedge ECLK) disable iff (RST)
        !$initstate && (Q != $past(Q)) |-> ($past(RST) || $past(DQSW))
    );

endmodule