module digital_circuit_sva (
    input logic CLK,
    input logic D,
    input logic Q,
    input logic Q_N,
    input logic SCD,
    input logic SCE,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);
    // Sequential logic: Q_ff is updated on the rising edge of CLK
    sequential_logic: assert property (
        @(posedge CLK) disable iff (!VPWR) Q_ff == D_ff
    );

    // Combinational logic: Q and Q_N are derived from Q_ff
    combinational_logic: assert property (
        @(posedge CLK) disable iff (!VPWR) (Q == Q_ff) && (Q_N == ~Q_ff)
    );

    // SCD and SCE control the input to the flip-flop
    control_logic: assert property (
        @(posedge CLK) disable iff (!VPWR) (Q_ff == (SCE ? SCD : D))
    );

    // VPWR is the active-high power supply signal
    power_supply: assert property (
        @(posedge CLK) disable iff (!VPWR) VPWR |-> 1'b1
    );

    // VPB is the active-high bus valid signal
    bus_valid: assert property (
        @(posedge CLK) disable iff (!VPWR) VPB |-> 1'b1
    );

    // VGND and VNB are ground and negative supply signals, respectively
    ground_and_supply: assert property (
        @(posedge CLK) disable iff (!VPWR) (VGND == 1'b0) && (VNB == 1'b0)
    );

    // SCE and SCD are inputs to the flip-flop
    input_signals: assert property (
        @(posedge CLK) disable iff (!VPWR) (SCE || SCD) |-> 1'b1
    );

    // D is the input to the flip-flop when SCE is low
    input_when_sce_low: assert property (
        @(posedge CLK) disable iff (!VPWR) (!SCE) |-> Q_ff == D
    );

    // SCD is the input to the flip-flop when SCE is high
    input_when_sce_high: assert property (
        @(posedge CLK) disable iff (!VPWR) SCE |-> Q_ff == SCD
    );

    // Q and Q_N are complements of each other
    complement_check: assert property (
        @(posedge CLK) disable iff (!VPWR) Q == ~Q_N
    );

    // Q_ff is updated only on the rising edge of CLK
    update_on_clk_edge: assert property (
        @(posedge CLK) disable iff (!VPWR) $stable(Q_ff)
    );
endmodule