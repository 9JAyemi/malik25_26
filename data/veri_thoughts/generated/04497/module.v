
module mux4to1 (
    input [3:0] data_in,
    input [1:0] sel,
    output reg data_out
);

    reg data_out_temp0;
    reg data_out_temp1;

    // Instantiate the two 2:1 multiplexers
    mux2to1 mux0 (
        .data_0(data_in[0]),
        .data_1(data_in[1]),
        .sel(sel[0]),
        .data_out(data_out_temp0)
    );
    mux2to1 mux1 (
        .data_0(data_in[2]),
        .data_1(data_in[3]),
        .sel(sel[0]),
        .data_out(data_out_temp1)
    );

    // Instantiate another 2:1 multiplexer to select the output of the two 2:1 multiplexers
    mux2to1 mux2 (
        .data_0(data_out_temp0),
        .data_1(data_out_temp1),
        .sel(sel[1]),
        .data_out(data_out)
    );

endmodule
module mux2to1 (
    input data_0,
    input data_1,
    input sel,
    output reg data_out
);

    always @(*) begin
        case (sel)
            1'b0: data_out = data_0;
            1'b1: data_out = data_1;
        endcase
    end

endmodule