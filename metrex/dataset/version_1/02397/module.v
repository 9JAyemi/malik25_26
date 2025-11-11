
module add_sub_mux(
    input [31:0] a,
    input [31:0] b,
    input sub,
    output [31:0] result
);

    wire [31:0] adder_out;
    wire mux_out;
    
    adder adder_inst(
        .a(a[31:16]),
        .b(b[31:16]),
        .sum(adder_out[31:16])
    );
    
    assign adder_out[15:0] = a[15:0] + b[15:0];
    
    assign mux_out = sub ? ~adder_out[0] : adder_out[0];
    
    assign result[31:16] = adder_out[31:16] + mux_out;
    assign result[15:0] = a[15:0] + b[15:0];

endmodule

module adder(
    input [15:0] a,
    input [15:0] b,
    output reg [15:0] sum
);

    always @ (a or b) begin
        sum <= a + b;
    end

endmodule
