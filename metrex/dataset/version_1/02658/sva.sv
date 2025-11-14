// Bindable SVA for module crc
// Focus: reset/init, register update rules, enable behavior, wiring equivalences,
// width/consistency assumptions, basic functional coverage.

bind crc crc_sva #(
  .data_size(data_size),
  .poly_size(poly_size),
  .crc_size (crc_size)
) crc_sva_i();

module crc_sva #(
  parameter int data_size = 8,
  parameter int poly_size = 4,
  parameter int crc_size  = poly_size-1
) ();

  // Clocking/reset context
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // ---------------------------------------------------------------------------
  // Elaboration-time sanity checks (fail-fast on nonsensical params)
  // ---------------------------------------------------------------------------
  initial begin
    if (poly_size < 2) $fatal(1, "poly_size must be >= 2");
    if (crc_size  != poly_size-1) $fatal(1, "crc_size must equal poly_size-1");
    if (data_size < crc_size) $fatal(1, "data_size (%0d) must be >= crc_size (%0d)", data_size, crc_size);
  end

  // ---------------------------------------------------------------------------
  // Reset behavior
  // ---------------------------------------------------------------------------
  a_reset_vals: assert property (reset |=> (data_reg=='0 && crc_reg=='0 && crc_calc=='0
                                            && poly_reg==poly && crc_check==crc_in));

  // poly_reg is only loaded in reset, must be stable otherwise
  a_poly_stable: assert property ($stable(poly_reg));

  // ---------------------------------------------------------------------------
  // Basic register update rules
  // ---------------------------------------------------------------------------
  // data_reg captures data_in every cycle
  a_data_cap:   assert property (data_reg == $past(data_in));

  // When crc_enable==0, CRC datapath registers hold their values
  a_crc_hold:   assert property (!crc_enable |-> ($stable(crc_reg) && $stable(crc_calc)));

  // When check_enable==0, crc_check holds its value
  a_chk_hold:   assert property (!check_enable |-> $stable(crc_check));

  // CRC update (mirrors RTL exactly). Require crc_size>=2 so slices are well-formed.
  generate
    if (crc_size >= 2) begin : g_crc_upd
      a_crc_upd: assert property (
        crc_enable |=> (crc_reg == $past(crc_calc)) &&
                       (crc_calc == $past({crc_calc[crc_size-2:0], data_reg, 1'b0} ^
                                          (poly_reg & {crc_calc[crc_size-2:0], 1'b0})))
      );

      a_chk_upd: assert property (
        check_enable |=> (crc_check == $past({crc_check[crc_size-2:0], data_reg, 1'b0} ^
                                             (poly_reg & {crc_check[crc_size-2:0], 1'b0})))
      );
    end
  endgenerate

  // ---------------------------------------------------------------------------
  // Combinational wiring checks
  // ---------------------------------------------------------------------------
  a_wire_crc_rem:  assert property (crc_remainder        == (crc_calc[crc_size-1:0] ^ crc_reg));
  a_wire_chk_rem:  assert property (crc_check_remainder  == (data_reg[crc_size-1:0] ^ crc_check));
  a_wire_match:    assert property (match == (crc_check_remainder == crc_in));

  // ---------------------------------------------------------------------------
  // Width/consistency and truncation assumptions (make intent explicit)
  // ---------------------------------------------------------------------------
  // Assume unused upper poly bits are zero to avoid unintended influence
  generate
    if (data_size > poly_size) begin : g_poly_upper_zero
      a_poly_upper_zero: assert property (poly_reg[data_size-1:poly_size] == '0);
    end
  endgenerate

  // Assume upper crc_in bits (above crc_size) are zero to make compare meaningful
  generate
    if (data_size > crc_size) begin : g_crc_in_upper_zero
      a_crc_in_upper_zero: assert property (check_enable |-> (crc_in[data_size-1:crc_size] == '0));
    end
  endgenerate

  // crc_out is assigned from {data_in, crc_calc} but truncated to data_size bits.
  // Check that the lower crc_size bits of crc_out equal crc_calc and the remaining
  // upper bits come from the lower portion of data_in (due to truncation).
  generate
    if (crc_size > 0 && data_size >= crc_size) begin : g_crc_out_map
      a_crc_out_low: assert property (crc_out[crc_size-1:0] == crc_calc);
      if (data_size > crc_size) begin
        localparam int HIW = data_size-1;
        localparam int LOW = crc_size;
        localparam int DIN_LO = (data_size-crc_size)-1;
        a_crc_out_hi: assert property (crc_out[HIW:LOW] == data_in[DIN_LO:0]);
      end
    end
  endgenerate

  // No X/Z on primary outputs in normal operation
  a_no_x_outs: assert property (!$isunknown({crc_out, match})));

  // ---------------------------------------------------------------------------
  // Concise functional coverage
  // ---------------------------------------------------------------------------
  c_reset_seen:        cover property ($fell(reset));
  c_crc_en_seen:       cover property (crc_enable);
  c_chk_en_seen:       cover property (check_enable);
  c_both_en_same:      cover property (crc_enable && check_enable);
  c_match_1:           cover property (match);
  c_match_0:           cover property (!match);
  c_crc_updates:       cover property (crc_enable ##1 (crc_reg != $past(crc_reg) || crc_calc != $past(crc_calc)));
  c_check_updates:     cover property (check_enable ##1 (crc_check != $past(crc_check)));

endmodule