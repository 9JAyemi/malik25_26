module sky130_fd_sc_hdll__dlxtn_sva (
    input logic clk,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Q,
    input logic GATE_N
);

    // Q matches the exact combinational equation implemented by the RTL.
    check_full_function: assert property (
        @(posedge clk)
        Q === (
            (GATE_N == 1'b0) ?
            ((D == 1'b0) & (VPWR == 1'b1) & (VGND == 1'b1) & (VPB == 1'b1) & (VNB == 1'b1)) :
            D
        )
    );

    // When GATE_N is high, Q passes D through.
    check_gate_high_passthrough: assert property (
        @(posedge clk)
        ((GATE_N === 1'b1)) |-> (Q === D)
    );

    // When GATE_N is low and all power pins are high, Q matches the qualified inversion of D.
    check_gate_low_valid_power_behavior: assert property (
        @(posedge clk)
        ((GATE_N === 1'b0) &&
         (VPWR === 1'b1) &&
         (VGND === 1'b1) &&
         (VPB  === 1'b1) &&
         (VNB  === 1'b1)) |-> (Q === (D == 1'b0))
    );

    // When GATE_N is low and D is high, Q is forced low.
    check_gate_low_data_high_forces_low: assert property (
        @(posedge clk)
        ((GATE_N === 1'b0) &&
         (D === 1'b1)) |-> (Q === 1'b0)
    );

    // When GATE_N is low and any power pin is low, Q is forced low.
    check_gate_low_power_low_forces_low: assert property (
        @(posedge clk)
        ((GATE_N === 1'b0) &&
         ((VPWR === 1'b0) ||
          (VGND === 1'b0) ||
          (VPB  === 1'b0) ||
          (VNB  === 1'b0))) |-> (Q === 1'b0)
    );

    // When GATE_N is low, D is low, and all power pins are high, Q is high.
    check_gate_low_data_low_with_valid_power_drives_high: assert property (
        @(posedge clk)
        ((GATE_N === 1'b0) &&
         (D === 1'b0) &&
         (VPWR === 1'b1) &&
         (VGND === 1'b1) &&
         (VPB  === 1'b1) &&
         (VNB  === 1'b1)) |-> (Q === 1'b1)
    );

endmodule