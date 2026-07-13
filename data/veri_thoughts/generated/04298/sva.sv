module mux4to1_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic [1:0] select,
    input logic enable,
    input logic [3:0] data_out
);

    // When disabled, the output must be all zeros.
    check_output_zero_when_disabled: assert property (
        @(posedge clk) !enable |-> (data_out == 4'b0000)
    );

    // Select 00 forwards data_in[0] into the LSB and zero-extends the output.
    check_select_00_maps_bit0: assert property (
        @(posedge clk) enable && (select == 2'b00) |-> (data_out == {3'b000, data_in[0]})
    );

    // Select 01 forwards data_in[1] into the LSB and zero-extends the output.
    check_select_01_maps_bit1: assert property (
        @(posedge clk) enable && (select == 2'b01) |-> (data_out == {3'b000, data_in[1]})
    );

    // Select 10 forwards data_in[2] into the LSB and zero-extends the output.
    check_select_10_maps_bit2: assert property (
        @(posedge clk) enable && (select == 2'b10) |-> (data_out == {3'b000, data_in[2]})
    );

    // Select 11 forwards data_in[3] into the LSB and zero-extends the output.
    check_select_11_maps_bit3: assert property (
        @(posedge clk) enable && (select == 2'b11) |-> (data_out == {3'b000, data_in[3]})
    );

    // The upper three output bits are always zero due to 1-bit to 4-bit assignment.
    check_output_is_zero_extended: assert property (
        @(posedge clk) (data_out[3:1] == 3'b000)
    );

endmodule