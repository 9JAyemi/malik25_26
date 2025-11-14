module top_module (
    input clk,
    input reset,
    input [3:0] data_in,
    input [3:0] A,
    input [3:0] B,
    output [7:0] out,
    input load
);

    wire GT, EQ;
    wire [3:0] counter_out;
    
    // Instantiate the magnitude comparator
    comparator comp_inst (
        .A(A),
        .B(B),
        .GT(GT),
        .EQ(EQ)
    );
    
    // Instantiate the binary counter
    counter counter_inst (
        .clk(clk),
        .reset(reset),
        .data_in(data_in),
        .load(load),
        .out(counter_out)
    );
    
    // Logic for selecting output
    assign out = (GT) ? {4'b0000, A} : (EQ) ? {4'b0000, B} : {4'b0000, counter_out};
    
endmodule

// 4-bit magnitude comparator module
module comparator (
    input [3:0] A,
    input [3:0] B,
    output GT,
    output EQ
);

    assign GT = (A > B);
    assign EQ = (A == B);
    
endmodule

// 4-bit binary counter module
module counter (
    input clk,
    input reset,
    input [3:0] data_in,
    input load,
    output reg [3:0] out
);

    always @(posedge clk) begin
        if (reset) begin
            out <= 4'b0000;
        end else if (load) begin
            out <= data_in;
        end else begin
            out <= out + 1;
        end
    end
    
endmodule