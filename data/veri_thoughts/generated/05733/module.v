
module axi_ethernet_ram_reader
   (state1a,
    goto_readDestAdrNib1,
    state0a,
    out_1,
    ram_valid_i,
    s_axi_aclk,
    AR,
    startReadDestAdrNib,
    Q );

  output state1a;
  output goto_readDestAdrNib1;
  output state0a;
  output out_1;

  input ram_valid_i;
  input s_axi_aclk;
  input [0:0]AR;
  input startReadDestAdrNib;
  input [7:0]Q;

  assign state1a = (state == 1'b1);
  assign goto_readDestAdrNib1 = (state == 1'b1);
  assign state0a = (state == 1'b0);
  assign out_1 = (state == 1'b0) && ram_valid_i;

  always @(posedge s_axi_aclk) begin
    if (state == 1'b1) begin
      if (startReadDestAdrNib) begin
        dest_addr_nibble <= AR;
        read_dest_addr_nibble <= 1'b1;
      end
      else begin
        ram_data <= {16'hdead, 16'hbeef};  // replaced $random with constants for simulation
        state <= 1'b0;
      end
    end
    else if (state == 1'b0) begin
      if (ram_valid_i) begin
        state <= 1'b1;
      end
    end
  end

  reg [15:0] ram_data;
  reg [3:0] dest_addr_nibble;
  reg read_dest_addr_nibble;
  reg [1:0] state = 2'b0;

endmodule