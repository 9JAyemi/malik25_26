module top_module(
    input [3:0] a1,
    input [3:0] a2,
    input [3:0] b1,
    input [3:0] b2,
    input sel1,
    input sel2,
    input select,
    output [3:0] out
);

    // First 2-to-1 multiplexer
    wire [3:0] mux1_out;
    mux2to1 mux1(
        .a(a1),
        .b(b1),
        .sel(sel1),
        .out(mux1_out)
    );
    
    // Second 2-to-1 multiplexer
    wire [3:0] mux2_out;
    mux2to1 mux2(
        .a(a2),
        .b(b2),
        .sel(sel2),
        .out(mux2_out)
    );
    
    // Control logic to select active multiplexer
    wire [3:0] active_mux_out;
    assign active_mux_out = select ? mux2_out : mux1_out;
    
    // Functional module to sum the outputs of the two multiplexers
    wire [7:0] sum;
    adder add(
        .a(active_mux_out),
        .b(mux2_out),
        .sum(sum)
    );
    
    // Output the sum of the active multiplexer's values
    assign out = sum[3:0];
    
endmodule

module mux2to1(
    input [3:0] a,
    input [3:0] b,
    input sel,
    output reg [3:0] out
);

    always @(*) begin
        if(sel) begin
            out = b;
        end else begin
            out = a;
        end
    end
    
endmodule

module adder(
    input [3:0] a,
    input [3:0] b,
    output reg [7:0] sum
);

    always @(*) begin
        sum = {4'b0, a} + {4'b0, b};
    end
    
endmodule