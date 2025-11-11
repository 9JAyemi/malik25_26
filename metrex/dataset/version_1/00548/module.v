module fifo_reg #
(
    parameter WIDTH = 8,
    parameter DEPTH = 4
)
(
    input  wire                       clk,
    input  wire                       rst,

    input  wire                       write_en, // input valid
    input  wire [WIDTH-1:0]           write_data,
    input  wire                       read_en, // output ready
    output wire [WIDTH-1:0]           read_data,
    output wire                       full, // input not ready
    output wire                       empty // output not valid
);

reg [WIDTH-1:0] data_reg[DEPTH-1:0];
reg valid_reg[DEPTH-1:0];
reg ptr_write_reg = 0;
reg ptr_read_reg = 0;
reg full_reg = 0;

assign read_data = data_reg[ptr_read_reg];
assign full = full_reg;
assign empty = ~valid_reg[ptr_read_reg];

wire [WIDTH-1:0] data_reg_0 = data_reg[0];
wire [WIDTH-1:0] data_reg_1 = data_reg[1];
wire [WIDTH-1:0] data_reg_2 = data_reg[2];
wire [WIDTH-1:0] data_reg_3 = data_reg[3];
wire valid_reg_0 = valid_reg[0];
wire valid_reg_1 = valid_reg[1];
wire valid_reg_2 = valid_reg[2];
wire valid_reg_3 = valid_reg[3];

reg shift;

integer i;

initial begin
    for (i = 0; i < DEPTH; i = i + 1) begin
        data_reg[i] <= 0;
        valid_reg[i] <= 0;
    end
end

always @(posedge clk) begin
    if (rst) begin
        ptr_write_reg <= 0;
        ptr_read_reg <= 0;
        full_reg <= 0;
        for (i = 0; i < DEPTH; i = i + 1) begin
            data_reg[i] <= 0;
            valid_reg[i] <= 0;
        end
    end else begin
        // transfer empty to full
        full_reg <= ~read_en & ~empty & write_en & (ptr_write_reg == ptr_read_reg);

        // transfer in if not full
        if (~full_reg & write_en) begin
            data_reg[ptr_write_reg] <= write_data;
            valid_reg[ptr_write_reg] <= 1;
            ptr_write_reg <= ptr_write_reg + 1;
            if (ptr_write_reg == DEPTH) begin
                ptr_write_reg <= 0;
            end
        end

        if (read_en & ~empty) begin
            ptr_read_reg <= ptr_read_reg + 1;
            if (ptr_read_reg == DEPTH) begin
                ptr_read_reg <= 0;
            end
        end
    end
end

endmodule