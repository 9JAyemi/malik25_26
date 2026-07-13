
module multiplexer (
    input a, b, c,
    output reg [3:0] out
);
    always @ (a or b or c)
        case ({c, b, a})
            3'b000: out <= 4'b0001;
            3'b001: out <= 4'b0010;
            3'b010: out <= 4'b0100;
            3'b011: out <= 4'b1000;
            3'b100: out <= 4'b0011;
            3'b101: out <= 4'b0110;
            3'b110: out <= 4'b1100;
            3'b111: out <= 4'b1111;
        endcase
endmodule
module flip_flops (
    input clk,
    input reset,
    input [7:0] d,
    output reg [7:0] q
);
    reg [2:0] counter;  // Fix the wire/reg mismatch
    
    always @ (posedge clk or posedge reset) 
        if (reset) begin
            q <= 8'b00000000;
            counter <= 0;
        end
        else begin
            if (counter == 3'b111) begin
                q <= d;
                counter <= 0;
            end
            else begin
                counter <= counter + 1;
            end
        end
endmodule
module top_module (
    input clk,
    input reset,
    input [7:0] d,
    input a, b, c,
    output [7:0] q
);
    wire [3:0] mux_out;
    wire [7:0] flip_flops_out;
    
    multiplexer mux (
        .a(a),
        .b(b),
        .c(c),
        .out(mux_out)
    );
    
    flip_flops ff (
        .clk(clk),
        .reset(reset),
        .d(d),
        .q(flip_flops_out)
    );
    
    assign q = mux_out & flip_flops_out;
endmodule