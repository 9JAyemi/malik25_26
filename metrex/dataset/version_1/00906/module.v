
module odd_parity_generator (
    input [7:0] in,
    output reg [8:0] out
);
    
    always @(*) begin
        out[8] = ^in;
        out[7:0] = in;
    end
    
endmodule
module bcd_counter (
    input clk,
    input reset,
    input [2:0] ena,
    output reg [3:0] q
);
    
    always @(posedge clk, posedge reset) begin
        if (reset) begin
            q <= 4'b0000;
        end else if (ena[2]) begin
            if (q == 4'b1001) begin
                q <= 4'b0000;
            end else begin
                q <= q + 1;
            end
        end else if (ena[1]) begin
            if (q[3] == 1 && q[2:0] == 3'b011) begin
                q <= {1'b0, 3'b000};
            end else if (q[2:0] == 3'b100) begin
                q <= {1'b1, 3'b000};
            end else begin
                q <= q + 1;
            end
        end else if (ena[0]) begin
            if (q[3:1] == 3'b100) begin
                q <= {1'b1, 3'b000};
            end else begin
                q <= q + 1;
            end
        end
    end
    
endmodule
module adder (
    input [8:0] a,
    input [3:0] b,
    output [7:0] out
);
    
    assign out = a[7:0] + b;
    
endmodule
module top_module (
    input clk,
    input reset,
    input [7:0] in,
    output [8:0] parity_out,
    output [2:0] ena,
    output [15:0] q,
    output [7:0] add_out
);
    
    wire [8:0] parity_in;
    wire [3:0] ones_digit;
    
    odd_parity_generator parity_gen(
        .in(in),
        .out(parity_in)
    );
    
    bcd_counter counter(
        .clk(clk),
        .reset(reset),
        .ena(ena),
        .q(q[3:0])
    );
    
    assign ones_digit = q[3:0];
    
    adder add(
        .a(parity_in),
        .b(ones_digit),
        .out(add_out)
    );
    
    assign parity_out = parity_in;
    assign q[15:4] = 12'b0;
    assign ena = 3'b0;
    
endmodule