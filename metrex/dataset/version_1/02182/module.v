
module edge_detection (
    input clk,
    input rst_n,
    input signal,
    output reg rise,
    output reg fall
);

reg prev_signal;

always @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin
        rise <= 0;
        fall <= 0;
        prev_signal <= 0;
    end else begin
        rise <= signal & ~prev_signal;
        fall <= ~signal & prev_signal;
        prev_signal <= signal;
    end
end

endmodule

module minimum_finding (
    input [7:0] a,
    input [7:0] b,
    input [7:0] c,
    input [7:0] d,
    output reg [7:0] min_val
);

always @(*) begin
    if(a < b && a < c && a < d) begin
        min_val = a;
    end else if(b < c && b < d) begin
        min_val = b;
    end else if(c < d) begin
        min_val = c;
    end else begin
        min_val = d;
    end
end

endmodule

module functional_module (
    input clk,
    input rst_n,
    input rise,
    input fall,
    input [7:0] min_val,
    output reg out
);

reg [7:0] max_val;

always @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin
        max_val <= 0;
    end else begin
        if(rise) begin
            max_val <= 8'hFF; // Set max_val to the maximum possible value
        end

        if(fall) begin
            out <= min_val; // Output the minimum value
        end

        if(max_val > min_val) begin
            out <= max_val; // Output the maximum value if it's greater than the minimum value
        end
    end
end

endmodule

module top_module (
    input clk,
    input rst_n,
    input [7:0] a, // It's 7 bits wide in the top_module instantiation, but 8 bits wide in the minimum_finding instantiation. This is an error.
    input [7:0] b,
    input [7:0] c,
    input [7:0] d,
    output wire out
);

reg signal;
wire rise, fall;
wire [7:0] min_val;

edge_detection ed(
    .clk(clk),
    .rst_n(rst_n),
    .signal(signal),
    .rise(rise),
    .fall(fall)
);

minimum_finding mf(
    .a(a), // Mismatch between the width of a (7 bits) and the width of the ports of the minimum_finding module (8 bits)
    .b(b),
    .c(c),
    .d(d),
    .min_val(min_val)
);

functional_module fm(
    .clk(clk),
    .rst_n(rst_n),
    .rise(rise),
    .fall(fall),
    .min_val(min_val),
    .out(out)
);

always @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin
        signal <= 0;
    end else begin
        signal <= a;
    end
end

endmodule
