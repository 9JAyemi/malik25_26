// SVA for asram16_if
// Bind these assertions to the DUT:
//   bind asram16_if asram16_if_sva #(.EXT_ADDR_WIDTH(EXT_ADDR_WIDTH)) sva();

module asram16_if_sva #(parameter EXT_ADDR_WIDTH = 17) ();

  // Access DUT signals via bind-scope
  default clocking cb @(posedge clk_i); endclocking
  default disable iff (rst_i);

  function automatic logic [EXT_ADDR_WIDTH-1:0] vaddr(input logic [31:0] a);
    return a[EXT_ADDR_WIDTH:1];
  endfunction

  // Reset behavior
  assert property (rst_i |=> sram_oe_o && sram_we_o &&
                   sram_address_o == '0 && sram_data_o == 16'h0 &&
                   sram_be_o == 2'b11 && sram_dir_out_o &&
                   !ack_o && reg_state == MEM_IDLE);

  // Simple invariants
  assert property (sram_cs_o == 1'b0);
  assert property (busy_o == (reg_state != MEM_IDLE));
  assert property (!(sram_we_o == 1'b0 && sram_oe_o == 1'b0));
  assert property (sram_we_o == 1'b0 |-> sram_dir_out_o == 1'b1);
  assert property (sram_oe_o == 1'b0 |-> sram_dir_out_o == 1'b0);

  // Protocol: do not issue rd and wr at the same time
  assert property (!(rd_i && (wr_i != 4'b0)));
  // Requests only sampled in IDLE (environment/protocol)
  assert property ((reg_state != MEM_IDLE) |-> (wr_i == 4'b0 && !rd_i));

  // Write: first beat setup/checks (next-cycle due to NBA semantics)
  assert property ((reg_state == MEM_IDLE && (wr_i != 4'b0) && (wr_i[3:2] != 2'b00))
                   |=> sram_we_o == 1'b0 &&
                       sram_address_o == vaddr(address_i) &&
                       sram_data_o == data_i[31:16] &&
                       sram_be_o == ~wr_i[3:2] &&
                       sram_dir_out_o == 1'b1);

  assert property ((reg_state == MEM_IDLE && (wr_i != 4'b0) && (wr_i[3:2] == 2'b00))
                   |=> sram_we_o == 1'b0 &&
                       sram_address_o == (vaddr(address_i) + 1'b1) &&
                       sram_data_o == data_i[15:0] &&
                       sram_be_o == ~wr_i[1:0] &&
                       sram_dir_out_o == 1'b1);

  // Write wait/hold/data phases drive WE as expected
  assert property ((reg_state inside {MEM_WRITE_WAIT1, MEM_WRITE_WAIT2}) |-> sram_we_o == 1'b0);
  assert property (reg_state == MEM_WRITE_SETUP2 |-> sram_we_o == 1'b0);
  assert property (reg_state == MEM_WRITE_HOLD   |-> sram_we_o == 1'b1);
  assert property ((reg_state inside {MEM_WRITE_DATA1, MEM_WRITE_DATA2}) |-> sram_we_o == 1'b1);

  // Write timing selection from IDLE
  assert property ((reg_state == MEM_IDLE && (wr_i != 0) && (wr_i[3:2] != 0) && timing_ctrl_i[3:0] == 0)
                   |=> reg_state == MEM_WRITE_DATA1);
  assert property ((reg_state == MEM_IDLE && (wr_i != 0) && (wr_i[3:2] != 0) && timing_ctrl_i[3:0] != 0)
                   |=> reg_state == MEM_WRITE_WAIT1);
  assert property ((reg_state == MEM_IDLE && (wr_i != 0) && (wr_i[3:2] == 0) && timing_ctrl_i[3:0] == 0)
                   |=> reg_state == MEM_WRITE_DATA2);
  assert property ((reg_state == MEM_IDLE && (wr_i != 0) && (wr_i[3:2] == 0) && timing_ctrl_i[3:0] != 0)
                   |=> reg_state == MEM_WRITE_WAIT2);

  // Write: transition to second beat depends on timing_ctrl_i[11:8]
  assert property ((reg_state == MEM_WRITE_DATA1 && reg_wr[1:0] != 2'b00 && timing_ctrl_i[11:8] == 0)
                   |=> reg_state == MEM_WRITE_SETUP2);
  assert property ((reg_state == MEM_WRITE_DATA1 && reg_wr[1:0] != 2'b00 && timing_ctrl_i[11:8] != 0)
                   |=> reg_state == MEM_WRITE_HOLD);

  // Read: initiation checks
  assert property ((reg_state == MEM_IDLE && rd_i)
                   |=> sram_oe_o == 1'b0 && sram_we_o == 1'b1 &&
                       sram_be_o == 2'b00 &&
                       sram_address_o == vaddr(address_i) &&
                       sram_dir_out_o == 1'b0);

  // Read enable stays low through wait/data1; deasserted after data2
  assert property ((reg_state inside {MEM_READ_WAIT1, MEM_READ_WAIT2, MEM_READ_DATA1}) |-> sram_oe_o == 1'b0);
  assert property ((reg_state == MEM_READ_DATA2) |=> sram_oe_o == 1'b1);

  // Read timing selection from IDLE
  assert property ((reg_state == MEM_IDLE && rd_i && timing_ctrl_i[7:4] == 0)
                   |=> reg_state == MEM_READ_DATA1);
  assert property ((reg_state == MEM_IDLE && rd_i && timing_ctrl_i[7:4] != 0)
                   |=> reg_state == MEM_READ_WAIT1);

  // Wait-state countdown/transition semantics
  assert property ((reg_state == MEM_READ_WAIT1  && reg_wait > 4'd1) |=> reg_state == MEM_READ_WAIT1  && reg_wait == $past(reg_wait)-1);
  assert property ((reg_state == MEM_READ_WAIT1  && reg_wait == 4'd1) |=> reg_state == MEM_READ_DATA1);
  assert property ((reg_state == MEM_READ_WAIT2  && reg_wait > 4'd1) |=> reg_state == MEM_READ_WAIT2  && reg_wait == $past(reg_wait)-1);
  assert property ((reg_state == MEM_READ_WAIT2  && reg_wait == 4'd1) |=> reg_state == MEM_READ_DATA2);
  assert property ((reg_state == MEM_WRITE_WAIT1 && reg_wait > 4'd1) |=> reg_state == MEM_WRITE_WAIT1 && reg_wait == $past(reg_wait)-1);
  assert property ((reg_state == MEM_WRITE_WAIT1 && reg_wait == 4'd1) |=> reg_state == MEM_WRITE_DATA1);
  assert property ((reg_state == MEM_WRITE_WAIT2 && reg_wait > 4'd1) |=> reg_state == MEM_WRITE_WAIT2 && reg_wait == $past(reg_wait)-1);
  assert property ((reg_state == MEM_WRITE_WAIT2 && reg_wait == 4'd1) |=> reg_state == MEM_WRITE_DATA2);
  assert property ((reg_state == MEM_WRITE_HOLD  && reg_wait > 4'd1) |=> reg_state == MEM_WRITE_HOLD  && reg_wait == $past(reg_wait)-1);
  assert property ((reg_state == MEM_WRITE_HOLD  && reg_wait == 4'd1) |=> reg_state == MEM_WRITE_SETUP2);

  // Read address increments to second half at READ_DATA1
  assert property ((reg_state == MEM_READ_DATA1) |=> sram_address_o == $past(reg_address) + 1);

  // ack behavior
  assert property (ack_o |-> reg_state == MEM_IDLE && busy_o == 1'b0);
  assert property (ack_o |-> ##1 !ack_o);

  // Write completion coverage: upper-only, lower-only, both-halves; Read completion
  assert property ((reg_state == MEM_IDLE && wr_i[3:2] != 0 && wr_i[1:0] == 0) |-> ##[1:$] (reg_state == MEM_WRITE_DATA1) ##1 ack_o);
  assert property ((reg_state == MEM_IDLE && wr_i[3:2] == 0 && wr_i[1:0] != 0) |-> ##[1:$] (reg_state == MEM_WRITE_DATA2) ##1 ack_o);
  assert property ((reg_state == MEM_IDLE && wr_i[3:2] != 0 && wr_i[1:0] != 0) |-> ##[1:$] (reg_state == MEM_WRITE_DATA2) ##1 ack_o);
  assert property ((reg_state == MEM_IDLE && rd_i) |-> ##[1:$] (reg_state == MEM_READ_DATA2) ##1 ack_o);

  // End-to-end read data concatenation check
  property p_read_concat;
    automatic logic [15:0] upper, lower;
    (reg_state == MEM_IDLE && rd_i)
      |-> ##[1:$] (reg_state == MEM_READ_DATA1, upper = sram_data_i)
          ##[1:$] (reg_state == MEM_READ_DATA2, lower = sram_data_i)
          ##1 (ack_o && data_o == {upper, lower});
  endproperty
  assert property (p_read_concat);

  // Coverage: hit all states and key paths
  cover property (reg_state == MEM_WRITE_DATA1);
  cover property (reg_state == MEM_WRITE_SETUP2);
  cover property (reg_state == MEM_WRITE_DATA2);
  cover property (reg_state == MEM_READ_DATA1);
  cover property (reg_state == MEM_READ_DATA2);
  cover property (reg_state == MEM_READ_WAIT1);
  cover property (reg_state == MEM_READ_WAIT2);
  cover property (reg_state == MEM_WRITE_WAIT1);
  cover property (reg_state == MEM_WRITE_WAIT2);
  cover property (reg_state == MEM_WRITE_HOLD);

  cover property ((reg_state == MEM_IDLE && wr_i[3:2] != 0 && wr_i[1:0] != 0 && timing_ctrl_i[3:0] != 0 && timing_ctrl_i[11:8] != 0)
                  |-> ##[1:$] reg_state == MEM_WRITE_HOLD ##[1:$] reg_state == MEM_WRITE_SETUP2 ##[1:$] ack_o);

  cover property ((reg_state == MEM_IDLE && rd_i && timing_ctrl_i[7:4] != 0)
                  |-> ##[1:$] reg_state == MEM_READ_WAIT1 ##[1:$] reg_state == MEM_READ_DATA2 ##1 ack_o);

endmodule