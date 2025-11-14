module clk_divider(
    input inclk,
    input ena,
    output enaout,
    output reg outclk
);

parameter clock_type = "auto";
parameter ena_register_mode = "always enabled";
parameter lpm_type = "cyclone10gx_clkena";
parameter ena_register_power_up = "high";
parameter disable_mode = "low";
parameter test_syn = "high";

reg ena_reg;

always @ (posedge inclk) begin
    if (ena_register_mode == "always enabled") begin
        ena_reg <= 1'b1;
    end else if (ena_register_mode == "synchronous") begin
        ena_reg <= ena;
    end else if (ena_register_mode == "asynchronous") begin
        ena_reg <= ena_reg | ena;
    end
end

assign enaout = ena_reg;

always @ (posedge inclk) begin
    if (ena == 1'b1) begin
        outclk <= ~outclk;
    end else begin
        outclk <= 1'b0;
    end
end

endmodule