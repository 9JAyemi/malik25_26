```systemverilog
module Video_System_CPU_nios2_oci_td_mode_sva (
    input logic clk,
    input logic rst_n,
    input logic [8:0] ctrl,
    output logic [3:0] td_mode
);
    // The logic is purely combinational as it only uses @* for the always block.

    // ctrl_bits_for_mux is derived from ctrl and is used in the always block.
    wire [2:0] ctrl_bits_for_mux;
    assign ctrl_bits_for_mux = ctrl[7:5];

    // td_mode is determined by the value of ctrl_bits_for_mux.
    always @*
    begin
        case (ctrl_bits_for_mux)
            3'b000: td_mode = 4'b0000;
            3'b001: td_mode = 4'b1000;
            3'b010: td_mode = 4'b0100;
            3'b011: td_mode = 4'b1100;
            3'b100: td_mode = 4'b0010;
            3'b101: td_mode = 4'b1010;
            3'b110: td_mode = 4'b0101;
            3'b111: td_mode = 4'b1111;
            default: td_mode = 4'b0000;
        endcase
    end

    // At reset, td_mode should be 0.
    reset: assert property (
        @(posedge clk) disable iff (!rst_n) td_mode == 4'b0000
    );

    // ctrl_bits_for_mux should always be within the valid range [0, 7].
    ctrl_bits_for_mux_range: assert property (
        @(posedge clk) disable iff (!rst_n) (ctrl_bits_for_mux >= 3'b000) && (ctrl_bits_for_mux <= 3'b111)
    );

    // td_mode should always be one of the valid values [0, 15].
    td_mode_range: assert property (
        @(posedge clk) disable iff (!rst_n) (td_mode >= 4'b0000) && (td_mode <= 4'b1111)
    );

    // ctrl_bits_for_mux should not change when td_mode is changing.
    ctrl_bits_for_mux_stable: assert property (
        @(posedge clk) disable iff (!rst_n) (ctrl_bits_for_mux == ctrl_bits_for_mux)
    );

    // td_mode should not change when ctrl_bits_for_mux is changing.
    td_mode_stable: assert property (
        @(posedge clk) disable iff (!rst_n) (td_mode == td_mode)
    );

    // ctrl_bits_for_mux should not be 3'b111 when td_mode is 4'b0000.
    ctrl_bits_for_mux_not_111_when_td_mode_0000: assert property (
        @(posedge clk) disable iff (!rst_n) (ctrl_bits_for_mux != 3'b111) |-> td_mode != 4'b0000
    );

    // td_mode should not be 4'b1111 when ctrl_bits_for_mux is 3'b000.
    td_mode_not_1111_when_ctrl_bits_for_mux_000: assert property (
        @(posedge clk) disable iff (!rst_n) (ctrl_bits_for_mux != 3'b000) |-> td_mode != 4'b1111
    );

    // ctrl_bits_for_mux should not be 3'b000 when td_mode is 4'b1111.
    ctrl_bits_for_mux_not_000_when_td_mode_1111: assert property (
        @(posedge clk) disable iff (!rst_n) (ctrl_bits_for_mux != 3'b000) |-> td_mode != 4'b1111
    );

    // td_mode should not be 4'b0000 when ctrl_bits_for_mux is 3'b111.
    td_mode_not_0000_when_ctrl_bits_for_mux_111: assert property (
        @(posedge clk) disable iff (!rst_n) (ctrl_bits_for_mux != 3'b111) |-> td_mode != 4'b0000
    );

endmodule
```