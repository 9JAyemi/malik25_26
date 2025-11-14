
module my_module (
    input [2:0] a,
    input [2:0] b,
    input [2:0] c,
    input [2:0] d,
    input [1:0] e,
    input clk,
    input rst,
    output reg y
);

reg [2:0] a_msb, b_msb;
reg [2:0] c_lsb, d_lsb;
reg [1:0] e_lsb;
reg e_msb;

always @ (posedge clk) begin
    if (rst) begin
        y <= 0;
    end else begin
        a_msb <= a[2:0];
        b_msb <= b[2:0];
        c_lsb <= c[2:0];
        d_lsb <= d[2:0];
        e_lsb <= e[1:0];
        e_msb <= e[0];

        if ((a_msb == b_msb) && (c_lsb == d_lsb) && (e_lsb == a[2]) && (e_msb == c[0])) begin
            y <= 1;
        end else begin
            y <= 0;
        end
    end
end

endmodule
