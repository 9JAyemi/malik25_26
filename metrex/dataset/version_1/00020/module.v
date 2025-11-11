module decalper_eb_ot_sdeen_pot_pi_dehcac_xnilix_rd_status_flags_ss
    (AR, E, clk, empty, out, ram_full_fb_i_reg, ram_full_fb_i_reg_0, rd_en, rsts);

    input [0:0] AR;
    input clk, empty, ram_full_fb_i_reg_0, rd_en;
    input ram_full_fb_i_reg;
    input [1:0] E;
    output rsts;
    output out;

    wire [0:0] AR;
    wire [1:0] E;
    wire clk, empty, ram_full_fb_i_reg, ram_full_fb_i_reg_0, rd_en;
    reg rsts, out;

    always @(posedge clk) begin
        if (rd_en && !empty) begin
            rsts <= 1'b0;
        end else if (ram_full_fb_i_reg && !ram_full_fb_i_reg_0) begin
            rsts <= 1'b1;
        end
    end

    always @(posedge clk) begin
        if (rd_en && !empty) begin
            out <= 1'b1;
        end else begin
            out <= 1'b0;
        end
    end

endmodule

module decalper_eb_ot_sdeen_pot_pi_dehcac_xnilix_rd_bin_cntr
    (AR, ram, E, clk, count, ram_empty_i_reg, rd_en, Q);

    input [0:0] AR;
    input [7:0] ram;
    input clk, E, ram_empty_i_reg, rd_en;
    input [1:0] count;
    output [5:0] Q;

    wire [0:0] AR;
    wire [7:0] ram;
    wire [1:0] count;
    wire clk, E, ram_empty_i_reg, rd_en;
    reg [5:0] Q;

    always @(posedge clk) begin
        if (rd_en && !ram_empty_i_reg) begin
            Q <= ram[count + AR];
        end
    end

endmodule