module shift_reg_mux(
    input clk,
    input areset,  // async active-high reset to zero
    input load,
    input ena,
    input [3:0] data,
    input sel_b1,
    input sel_b2,
    output reg [3:0] q
);

reg [3:0] shift_reg;
wire mux_out;

// 4-bit shift register with synchronous reset, synchronous load, and enable
always @(posedge clk, posedge areset) begin
    if (areset) begin
        shift_reg <= 4'b0;
    end else if (load) begin
        shift_reg <= data;
    end else if (ena) begin
        shift_reg <= {shift_reg[2:0], data[0]};
    end
end

// 2-to-1 multiplexer with constant value of 0x0F
assign mux_out = (sel_b1 & sel_b2) ? 4'hF : shift_reg;

// output of the multiplexer
always @(posedge clk, posedge areset) begin
    if (areset) begin
        q <= 4'b0;
    end else begin
        q <= mux_out;
    end
end

endmodule