
module shift_register (
    input wire s_axi_aclk,
    input wire [7:0] D,
    input wire shift_reg_ld0,
    input wire [0:0] SR,
    input wire [0:0] E,
    input wire detect_start,
    input wire detect_stop_reg,
    input wire sda_sample,
    input wire master_slave_reg,
    input wire [2:0] out,
    output wire arb_lost_reg,
    output wire abgc_i_reg_0,
    output wire shift_reg_ld,
    output reg [7:0] Q
);

reg [7:0] shift_reg;

always @(posedge s_axi_aclk) begin
    if (SR == 1'b1) begin
        shift_reg <= 8'b0;
    end else if (E == 1'b1) begin
        if (shift_reg_ld0 == 1'b1) begin
            shift_reg <= 8'b0;
        end else begin
            if (detect_start == 1'b1) begin
                shift_reg <= 8'b0;
            end else begin
                shift_reg <= {shift_reg[6:0], sda_sample};
            end
        end
    end
    Q <= shift_reg; // Move the assignment inside the always block
end

assign abgc_i_reg_0 = (out == 3'b000) ? 1'b0 : (detect_start == 1'b1) ? 1'b1 : shift_reg;

assign shift_reg_ld = (out == 3'b000) ? 1'b0 : (out == 3'b001) ? 1'b1 : (detect_stop_reg == 1'b1) ? 1'b1 : (shift_reg_ld0 == 1'b1) ? 1'b0 : 1'bx;

assign arb_lost_reg = (master_slave_reg == 1'b1) ? ((shift_reg_ld0 == 1'b1) || (detect_start == 1'b1)) ? 1'b0 : ((shift_reg[7] == 1'b0) && (sda_sample == 1'b1)) ? 1'b1 : shift_reg : 1'bx;

endmodule
