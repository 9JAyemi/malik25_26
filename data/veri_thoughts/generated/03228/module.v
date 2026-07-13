
module simple_multiplier (
    input  wire        clk,
    input  wire [ 7:0] A,
    input  wire [ 7:0] B,
    output wire [15:0] Z
);

    reg [15:0] Z_sync;

    always @(posedge clk)
        Z_sync <= A * B;

    assign Z = Z_sync;

endmodule