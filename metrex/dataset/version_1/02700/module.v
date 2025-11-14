module vending_machine(
    input clk,
    input rst,
    input nickel,
    input dime,
    input quarter,
    input select_A,
    input select_B,
    input select_C,
    output dispense,
    output change_10,
    output change_25,
    output product_A,
    output product_B,
    output product_C
);

reg [7:0] total_amount;
reg [1:0] product_selected;
reg [1:0] change_returned;
wire [7:0] cost = 50;

assign dispense = (total_amount >= cost) & (select_A | select_B | select_C);
assign change_10 = (change_returned == 2'b10);
assign change_25 = (change_returned == 2'b01);
assign product_A = (product_selected == 2'b01);
assign product_B = (product_selected == 2'b10);
assign product_C = (product_selected == 2'b11);

always @(posedge clk) begin
    if (rst) begin
        total_amount <= 0;
        product_selected <= 0;
        change_returned <= 0;
    end else begin
        if (nickel) begin
            total_amount <= total_amount + 5;
            change_returned <= 2'b00;
        end
        if (dime) begin
            total_amount <= total_amount + 10;
            change_returned <= 2'b00;
        end
        if (quarter) begin
            total_amount <= total_amount + 25;
            change_returned <= 2'b00;
        end
        if (select_A) begin
            if (total_amount >= cost) begin
                product_selected <= 2'b01;
                total_amount <= total_amount - cost;
                change_returned <= total_amount;
            end else begin
                product_selected <= 0;
                total_amount <= 0;
                change_returned <= 0;
            end
        end
        if (select_B) begin
            if (total_amount >= cost) begin
                product_selected <= 2'b10;
                total_amount <= total_amount - cost;
                change_returned <= total_amount;
            end else begin
                product_selected <= 0;
                total_amount <= 0;
                change_returned <= 0;
            end
        end
        if (select_C) begin
            if (total_amount >= cost) begin
                product_selected <= 2'b11;
                total_amount <= total_amount - cost;
                change_returned <= total_amount;
            end else begin
                product_selected <= 0;
                total_amount <= 0;
                change_returned <= 0;
            end
        end
    end
end

endmodule