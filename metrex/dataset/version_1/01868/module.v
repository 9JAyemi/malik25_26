module blockmem2rptr1w(
                       input wire           clk,
                       input wire           reset_n,

                       input wire  [07 : 0] read_addr0,
                       output wire [31 : 0] read_data0,

                       output wire [31 : 0] read_data1,

                       input wire           rst,
                       input wire           cs,
                       input wire           wr,
                       input wire  [07 : 0] write_addr,
                       input wire  [31 : 0] write_data
                      );


  //----------------------------------------------------------------
  // Memories and regs including update variables and write enable.
  //----------------------------------------------------------------
  reg [31 : 0] mem [0 : 255];
  reg [31 : 0] tmp_read_data0;
  reg [31 : 0] tmp_read_data1;

  reg [7 : 0] ptr_reg;
  reg [7 : 0] ptr_new;
  reg         ptr_we;


  //----------------------------------------------------------------
  // Concurrent connectivity for ports etc.
  //----------------------------------------------------------------
  assign read_data0 = tmp_read_data0;
  assign read_data1 = mem[ptr_reg];


  //----------------------------------------------------------------
  // mem_update
  //
  // Clocked update of memory This should cause
  // the memory to be implemented as a block memory.
  //----------------------------------------------------------------
  always @ (posedge clk)
    begin : mem_update
      if (wr)
        mem[write_addr] <= write_data;

      tmp_read_data0 <= mem[read_addr0];
    end


  //----------------------------------------------------------------
  // reg_update
  //----------------------------------------------------------------
  always @ (posedge clk or negedge reset_n)
    begin : reg_mem_update
      if (!reset_n)
        ptr_reg <= 8'h00;

      else
        if (ptr_we)
          ptr_reg <= ptr_new;
    end


  //----------------------------------------------------------------
  // ptr_logic
  //----------------------------------------------------------------
  always @*
    begin : ptr_logic
      ptr_new = 8'h00;
      ptr_we  = 1'b0;

      if (rst)
        begin
          ptr_new = 8'h00;
          ptr_we  = 1'b1;
        end

      if (cs)
        begin
          ptr_new = ptr_reg + 1'b1;
          ptr_we  = 1'b1;
        end
    end

endmodule