module r_FAULT_STATUS_assertions (
    input logic clk,
    input logic reset,
    input logic wenb,
    input logic [7:0] in_data,
    output reg [7:0] reg_0x1F
);
    always @(posedge clk) begin
        if (reset == 1'b1) begin
            reg_0x1F <= 8'h00;
        end
        else begin
            if (wenb == 1'b0) begin
                reg_0x1F <= in_data;
            end
            else begin
                reg_0x1F <= reg_0x1F;
            end
        end
    end

    ///// Register behavior /////
    // Register reg_0x1F should be reset to 0x00 on reset.
    reset_reg_0x1F: assert property (
        @(posedge clk) disable iff (!reset) reg_0x1F == 8'h00
    );

    // Register reg_0x1F should be updated with in_data when wenb is 0.
    update_reg_0x1F: assert property (
        @(posedge clk) disable iff (!reset) (wenb == 1'b0) |-> reg_0x1F == in_data
    );

    // Register reg_0x1F should remain unchanged when wenb is 1.
    no_update_reg_0x1F: assert property (
        @(posedge clk) disable iff (!reset) (wenb == 1'b1) |-> reg_0x1F == reg_0x1F
    );
endmodule