module mux_adder_sva (
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [1:0] add_in,
    input logic clk,
    input logic reset,
    input logic select,
    input logic [7:0] out
);

    function automatic logic [3:0] selected_data (
        input logic [2:0] sel_f,
        input logic [3:0] data0_f,
        input logic [3:0] data1_f,
        input logic [3:0] data2_f,
        input logic [3:0] data3_f,
        input logic [3:0] data4_f,
        input logic [3:0] data5_f
    );
        begin
            case (sel_f)
                3'b000: selected_data = data0_f;
                3'b001: selected_data = data1_f;
                3'b010: selected_data = data2_f;
                3'b011: selected_data = data3_f;
                3'b100: selected_data = data4_f;
                3'b101: selected_data = data5_f;
                default: selected_data = 4'b0000;
            endcase
        end
    endfunction

    // Reset forces the registered output low.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |-> (out == 8'b00000000)
    );

    // In bypass mode, out captures the zero-extended muxed data.
    check_bypass_mode_output: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b0) |=> (
            out == {
                4'b0000,
                selected_data(
                    $past(sel),
                    $past(data0),
                    $past(data1),
                    $past(data2),
                    $past(data3),
                    $past(data4),
                    $past(data5)
                )
            }
        )
    );

    // In add mode, out captures the muxed data plus add_in.
    check_add_mode_output: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b1) |=> (
            out == (
                {
                    4'b0000,
                    selected_data(
                        $past(sel),
                        $past(data0),
                        $past(data1),
                        $past(data2),
                        $past(data3),
                        $past(data4),
                        $past(data5)
                    )
                } + {6'b000000, $past(add_in)}
            )
        )
    );

    // Bypass mode always zero-extends into the upper nibble.
    check_bypass_zero_extension: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b0) |=> (out[7:4] == 4'b0000)
    );

    // Add mode always zero-extends into the upper two bits.
    check_add_mode_zero_extension: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b1) |=> (out[7:6] == 2'b00)
    );

    // Invalid mux select codes produce zero in bypass mode.
    check_invalid_sel_bypass_zero: assert property (
        @(posedge clk) disable iff (reset)
        ((select == 1'b0) && ((sel == 3'b110) || (sel == 3'b111))) |=> (out == 8'b00000000)
    );

    // Invalid mux select codes add only add_in in add mode.
    check_invalid_sel_add_uses_add_in_only: assert property (
        @(posedge clk) disable iff (reset)
        ((select == 1'b1) && ((sel == 3'b110) || (sel == 3'b111))) |=> (out == {6'b000000, $past(add_in)})
    );

endmodule