module emesh_wralign_sva (
    input  logic        clk,
    input  logic [1:0]  datamode,
    input  logic [63:0] data_in,
    input  logic [63:0] data_out
);
    // LSB byte always passes through.
    check_byte0_passthrough: assert property (
        @(posedge clk) data_out[7:0] == data_in[7:0]
    );

    // For datamode==00, all bytes replicate data_in[7:0].
    check_mode00_replicate: assert property (
        @(posedge clk) (datamode == 2'b00) |-> (data_out == {8{data_in[7:0]}})
    );

    // For datamode==01, output bytes alternate B1,B0 pattern.
    check_mode01_pattern: assert property (
        @(posedge clk) (datamode == 2'b01) |-> (data_out == {
            data_in[15:8], data_in[7:0],
            data_in[15:8], data_in[7:0],
            data_in[15:8], data_in[7:0],
            data_in[15:8], data_in[7:0]
        })
    );

    // For datamode==10, low 32b (B3..B0) duplicated into upper 32b.
    check_mode10_pattern: assert property (
        @(posedge clk) (datamode == 2'b10) |-> (data_out == {
            data_in[31:24], data_in[23:16], data_in[15:8], data_in[7:0],
            data_in[31:24], data_in[23:16], data_in[15:8], data_in[7:0]
        })
    );

    // For datamode==11, full pass-through of data_in.
    check_mode11_passthrough: assert property (
        @(posedge clk) (datamode == 2'b11) |-> (data_out == data_in)
    );
endmodule