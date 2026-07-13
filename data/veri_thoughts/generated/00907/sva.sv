module interrupt_sva (
    input logic clock,

    input logic IEN_d,
    input logic IOF_d,
    input logic RTI_d,
    input logic branch_d,
    input logic IRQ,
    input logic [11:0] PC,

    input logic branch_ISR,
    input logic [11:0] ISR_adr,

    // Internal DUT signals
    input logic [11:0] return_adr,
    input logic IEN_reg,
    input logic IRQ_reg,
    input logic I
);
    // IRQ_reg must capture IRQ on every rising edge.
    check_irq_reg_captures_IRQ: assert property (
        @(posedge clock) (IRQ_reg == IRQ)
    );

    // IEN_reg is cleared when an interrupt is taken (I=1).
    check_IEN_reg_cleared_on_interrupt: assert property (
        @(posedge clock) (I == 1'b1) |-> (IEN_reg == 1'b0)
    );

    // IEN_reg is cleared when IOF_d is asserted and no interrupt is taken.
    check_IEN_reg_cleared_on_IOF_only: assert property (
        @(posedge clock) (IOF_d == 1'b1 && I == 1'b0) |-> (IEN_reg == 1'b0)
    );

    // IEN_reg is set when IEN_d is asserted and no clear condition applies.
    check_IEN_reg_set_on_IEN_only: assert property (
        @(posedge clock) (IEN_d == 1'b1 && IOF_d == 1'b0 && I == 1'b0) |-> (IEN_reg == 1'b1)
    );

    // return_adr captures PC when an interrupt is taken.
    check_return_adr_captured_on_interrupt: assert property (
        @(posedge clock) (I == 1'b1) |-> (return_adr == PC)
    );

    // branch_ISR is asserted iff I or RTI_d is true.
    check_branch_ISR_definition: assert property (
        @(posedge clock) (branch_ISR == (I || RTI_d))
    );

    // On interrupt, ISR_adr must be vector 12'h1.
    check_ISR_adr_on_interrupt: assert property (
        @(posedge clock) (I == 1'b1) |-> (ISR_adr == 12'h001)
    );

    // On RTI only (no interrupt), ISR_adr must be return_adr.
    check_ISR_adr_on_RTI_only: assert property (
        @(posedge clock) (I == 1'b0 && RTI_d == 1'b1) |-> (ISR_adr == return_adr)
    );

    // With no event (no I, no RTI), outputs are deasserted/zero.
    check_ISR_default_when_no_event: assert property (
        @(posedge clock) (I == 1'b0 && RTI_d == 1'b0) |-> (branch_ISR == 1'b0 && ISR_adr == 12'h000)
    );

    // branch_ISR low implies ISR_adr is zero.
    check_branch_zero_implies_zero_addr: assert property (
        @(posedge clock) (branch_ISR == 1'b0) |-> (ISR_adr == 12'h000)
    );

    // I can be high only if IEN_reg and IRQ_reg are high and branch_d is low.
    check_I_high_requires_inputs: assert property (
        @(posedge clock) (I == 1'b1) |-> (IEN_reg == 1'b1 && IRQ_reg == 1'b1 && branch_d == 1'b0)
    );

    // I must be low when IEN_reg is low.
    check_I_low_when_IEN_reg_zero: assert property (
        @(posedge clock) (IEN_reg == 1'b0) |-> (I == 1'b0)
    );

    // I must be low when IRQ_reg is low.
    check_I_low_when_IRQ_reg_zero: assert property (
        @(posedge clock) (IRQ_reg == 1'b0) |-> (I == 1'b0)
    );

    // I must be low when branch_d is high.
    check_I_low_when_branch_d_one: assert property (
        @(posedge clock) (branch_d == 1'b1) |-> (I == 1'b0)
    );
endmodule