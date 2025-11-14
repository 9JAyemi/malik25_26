module accu(
    input               clk         ,   
    input               rst_n       ,
    input       [7:0]   data_in     ,
    input               valid_a     ,
    input               ready_b     ,
 
    output              ready_a     ,
    output  reg         valid_b     ,
    output  reg [9:0]   data_out
);

reg [7:0] data_reg;
reg [3:0] count_reg;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        data_reg <= 8'b0;
        count_reg <= 4'b0;
        valid_b <= 1'b0;
        data_out <= 10'b0;
    end
    else begin
        if (valid_a) begin
            data_reg <= data_reg + data_in;
            count_reg <= count_reg + 1;
        end
        if (count_reg == 4'b1111) begin
            data_out <= {data_reg, 2'b0};
            valid_b <= 1'b1;
        end
    end
end

assign ready_a = ~valid_b & ready_b;

endmodule