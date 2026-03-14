module comparator (
    input [1:0] A,
    input [1:0] B,
    output reg [1:0] out
);
    always @(*) begin
        if (A > B) begin
            out <= 2'b01;
        end else if (A < B) begin
            out <= 2'b10;
        end else begin
            out <= 2'b00;
        end
    end
endmodule

module subtractor (
    input [1:0] A,
    input [1:0] B,
    output reg [2:0] out
);
    wire [1:0] A_comp;
    assign A_comp = ~A + 2'b1;
    
    always @(*) begin
        out[2] = 0;
        if (A < B) begin
            out[2] = 1;
            out[1:0] = A_comp + B;
        end else begin
            out[1:0] = A - B;
        end
    end
endmodule

module top_module (
    input [1:0] A,
    input [1:0] B,
    output reg [2:0] out
);
    wire [1:0] comp_out;
    wire [2:0] sub_out;

    comparator comp(
        .A(A), 
        .B(B), 
        .out(comp_out)
    );

    subtractor sub(
        .A(A), 
        .B(B), 
        .out(sub_out)
    );
    
    always @(*) begin
        if (sub_out[2] == 1) begin
            out = ~sub_out[1:0] + 3'b001;
        end else begin
            out = sub_out;
        end
    end
endmodule
