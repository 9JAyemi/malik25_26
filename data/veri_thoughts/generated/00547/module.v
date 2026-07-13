module counter48 #(
        parameter DATASIZE  = 16    // width of the counter, must be <=48 bits!
    ) (
        input wire                  clk,
        input wire                  res_n,
        input wire                  increment,
        input wire  [DATASIZE-1:0]  load,
        input wire                  load_enable,
        output wire [DATASIZE-1:0]  value
);

    reg [DATASIZE-1:0]  value_reg;
    reg                 load_enable_reg;

    assign value    = value_reg;

    always @(posedge clk or negedge res_n) begin
        if (!res_n) begin
            value_reg       <= {DATASIZE{1'b0}};
            load_enable_reg <= 1'b0;
        end
        else begin
            load_enable_reg <= load_enable;
            if (load_enable_reg) begin
                value_reg   <= load;
            end else if (increment) begin
                value_reg   <= value_reg + 1'b1;
            end
        end
    end

endmodule