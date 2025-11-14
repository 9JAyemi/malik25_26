// SystemVerilog Assertions for top_module
// Focused, high-value checks + targeted coverage

// Place inside top_module or bind to it
// default clocking for concise $past usage
default clocking cb @(posedge clk); endclocking

// Reset behavior (async in RTL; sampled on clk)
ap_reset_values: assert property (reset |-> (reg_out == 8'h34 && counter == 4'h0));

// Register load when not in or coming out of reset
ap_reg_load: assert property (!reset && !$past(reset) |-> reg_out == $past(d));

// Counter increments modulo-16 when not in or coming out of reset
ap_ctr_inc: assert property (!reset && !$past(reset) |-> counter == (($past(counter) + 4'd1) & 4'hF));

// Muxed output q reflects prior-cycle select and sources
ap_q_mux: assert property (1 |-> q == ($past(select) ? $past(reg_out) : {4'h0, $past(counter)}));

// If counter path selected, upper bits of q are zero
ap_q_upper_zero: assert property ($past(!select) |-> q[7:4] == 4'h0);

// Combinational counter_out = (counter + reg_out[3:0]) mod 16 (checked 1-cycle late)
ap_counter_out_comb: assert property (1 |-> counter_out == (($past(counter) + $past(reg_out[3:0])) & 4'hF));

// RAM write takes effect in next cycle at past address
ap_ram_write_effect: assert property (write_en |=> ram[$past(write_addr[2:0])] == $past(write_data));

// RAM read returns old memory contents (read-during-write to same addr returns old data)
ap_ram_read_old: assert property (read_en |=> ram_out == $past(ram[read_addr[2:0]]));

// RAM: no unintended writes (only selected entry may change on a write)
genvar gi;
generate
  for (gi = 0; gi < 8; gi++) begin : gen_ram_no_unintended
    ap_ram_only_addr_updates: assert property (write_en |=> (gi == $past(write_addr[2:0]))
                                              ? 1'b1
                                              : (ram[gi] == $past(ram[gi])));
  end
endgenerate

// RAM: when no write, all entries hold value
generate
  for (gi = 0; gi < 8; gi++) begin : gen_ram_holds_no_write
    ap_ram_holds_no_write: assert property (!$past(write_en) |-> ram[gi] == $past(ram[gi]));
  end
endgenerate

// ---------------------------------
// Targeted coverage
// ---------------------------------
cv_reset_pulse:     cover property (reset ##1 !reset);
cv_select_0_path:   cover property (!select ##1 select);
cv_select_1_path:   cover property (select ##1 !select);
cv_ctr_wrap:        cover property (!reset && $past(counter)==4'hF && counter==4'h0);

cv_write_addr0:     cover property (write_en && write_addr[2:0]==3'd0);
cv_write_addr7:     cover property (write_en && write_addr[2:0]==3'd7);
cv_read_addr0:      cover property (read_en && read_addr[2:0]==3'd0);
cv_read_addr7:      cover property (read_en && read_addr[2:0]==3'd7);

// Simultaneous read/write same address (read returns old data)
cv_rdwr_same:       cover property (read_en && write_en && (read_addr[2:0] == write_addr[2:0]));

// Read-after-write different cycles, same address
cv_raw:             cover property (write_en ##1 (read_en && (read_addr[2:0] == $past(write_addr[2:0]))));