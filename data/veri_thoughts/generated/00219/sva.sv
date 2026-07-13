module RegisterAdd_4_sva (
    input logic [3:0] Q_reg,
    input logic [3:0] D,
    input logic CLK,
    input logic RST
);

    // A reset cycle clears the register to zero.
    check_reset_clears_q: assert property (
        @(posedge CLK)
        !$initstate && $past(RST) |-> (Q_reg == 4'b0000)
    );

    // Outside reset, Q_reg updates as the prior value plus the prior D input.
    check_accumulate_update: assert property (
        @(posedge CLK) disable iff (RST)
        !$initstate && !$past(RST) |-> (Q_reg == ($past(Q_reg) + $past(D)))
    );

    // With zero input outside reset, the register holds its prior value.
    check_hold_when_d_zero: assert property (
        @(posedge CLK) disable iff (RST)
        !$initstate && !$past(RST) && ($past(D) == 4'b0000) |-> (Q_reg == $past(Q_reg))
    );

    // From a zero state outside reset, the next value matches the prior D input.
    check_load_from_zero: assert property (
        @(posedge CLK) disable iff (RST)
        !$initstate && !$past(RST) && ($past(Q_reg) == 4'b0000) |-> (Q_reg == $past(D))
    );

endmodule