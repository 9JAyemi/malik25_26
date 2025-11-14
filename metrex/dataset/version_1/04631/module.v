
module fifo_64in_out_blk_mem_gen
(
    dout,
    wr_clk,
    rd_clk,
    I1,
    tmp_ram_rd_en,
    Q,
    O2,
    O1,
    din
);
    output [63:0]dout;
    input wr_clk;
    input rd_clk;
    input I1;
    input tmp_ram_rd_en;
    input [0:0]Q;
    input [11:0]O2;
    input [11:0]O1;
    input [63:0]din;

    reg [7:0] data [0:7];
    reg [2:0] read_address;
    reg [2:0] write_address;
    wire [2:0] num_entries;
    wire [2:0] next_write_address;
    wire [2:0] next_num_entries;
    reg [7:0] read_data;
    reg [7:0] write_data;
    reg write_enable;
    reg read_enable;

    assign num_entries = write_address - read_address;

    // Write logic
    always @(posedge wr_clk) begin
        if (I1 && (num_entries != 8'b1000)) begin
            data[write_address] <= din[7:0];
            write_address <= next_write_address;
            write_enable <= 1'b1;
        end else begin
            write_enable <= 1'b0;
        end
    end

    // Read logic
    always @(posedge rd_clk) begin
        if (tmp_ram_rd_en && (num_entries != 8'b000)) begin
            read_data <= data[read_address];
            read_address <= read_address + 1'b1;
            read_enable <= 1'b1;
        end else begin
            read_enable <= 1'b0;
        end
    end

    // Update state
    assign next_write_address = write_address + 1'b1;
    assign next_num_entries = (I1 && (num_entries != 8'b1000)) ? num_entries + 1'b1 : 
                               (tmp_ram_rd_en && (num_entries != 8'b000)) ? num_entries - 1'b1 : num_entries;

    // Output data
    assign dout = {56'h0, read_data};

endmodule