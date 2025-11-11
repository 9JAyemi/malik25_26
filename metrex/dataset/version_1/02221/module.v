module lfsr_count255(
                     input i_sys_clk,
                     input i_sys_rst,
                     output reg o_lfsr_256_done);

    reg [7:0]                   lfsr_reg_i;
    wire                        lfsr_d0_i,lfsr_256_equal_i;

    // Feedback polynomial: x^7 + x^5 + x^4 + x^3 + 1
    xnor(lfsr_d0_i,lfsr_reg_i[7],lfsr_reg_i[5],lfsr_reg_i[4],lfsr_reg_i[3]);
    assign lfsr_256_equal_i = (lfsr_reg_i == 8'hFF);

    always @(posedge i_sys_clk,posedge i_sys_rst) begin
        if(i_sys_rst) begin
            lfsr_reg_i <= 0;
            o_lfsr_256_done <= 0;
        end
        else begin
            lfsr_reg_i <= lfsr_256_equal_i ? 8'h0 : {lfsr_reg_i[6:0],lfsr_d0_i};
            o_lfsr_256_done <= lfsr_256_equal_i;
        end
    end
endmodule