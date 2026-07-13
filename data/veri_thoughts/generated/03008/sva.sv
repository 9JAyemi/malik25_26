module input_mux_sva #(
    parameter int C_FSM_SWITCH_WIDTH = 20,
    parameter int C_INTERFACE = 0
) (
    input logic clk,
    input logic [4:0] sel,
    input logic [C_FSM_SWITCH_WIDTH-1:0] in_pin,
    input logic out_int
);

generate
    if (C_INTERFACE == 1) begin : gen_raspberrypi
        // Valid Raspberry Pi selections drive the corresponding input bit.
        check_rpi_selected_pin: assert property (
            @(posedge clk) (sel <= 5'h19) |-> (out_int == in_pin[sel])
        );

        // Unmapped Raspberry Pi selections drive zero.
        check_rpi_default_zero: assert property (
            @(posedge clk) (sel > 5'h19) |-> (out_int == 1'b0)
        );

        // Output stays stable when selector and inputs stay stable.
        check_rpi_stable_for_stable_inputs: assert property (
            @(posedge clk) ($stable(sel) && $stable(in_pin)) |-> $stable(out_int)
        );
    end
    else begin : gen_arduino
        // Valid Arduino selections drive the corresponding input bit.
        check_arduino_selected_pin: assert property (
            @(posedge clk) (sel <= 5'h13) |-> (out_int == in_pin[sel])
        );

        // Unmapped Arduino selections drive zero.
        check_arduino_default_zero: assert property (
            @(posedge clk) (sel > 5'h13) |-> (out_int == 1'b0)
        );

        // Output stays stable when selector and inputs stay stable.
        check_arduino_stable_for_stable_inputs: assert property (
            @(posedge clk) ($stable(sel) && $stable(in_pin)) |-> $stable(out_int)
        );
    end
endgenerate

endmodule