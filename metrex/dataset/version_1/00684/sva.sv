// SVA for mbus_wire_ctrl
// Bind-in assertions; concise, checks reset, priority, muxing, and covers each path.

`ifndef MBUS_WIRE_CTRL_SVA
`define MBUS_WIRE_CTRL_SVA

module mbus_wire_ctrl_asserts (
  input RESETn,
  input DOUT_FROM_BUS,
  input CLKOUT_FROM_BUS,
`ifdef POWER_GATING
  input DIN,
  input CLKIN,
  input RELEASE_ISO_FROM_SLEEP_CTRL,
  input EXTERNAL_INT,
`endif
  input DOUT,
  input CLKOUT
);

  // Combinational equivalence checks (robust to Xs via 4-state compares)
  always_comb begin
    // Reset dominates everything
    if (RESETn===1'b0) begin
      assert #0 (CLKOUT===1'b1) else $error("CLKOUT must be 1 during reset");
      assert #0 (DOUT  ===1'b1) else $error("DOUT must be 1 during reset");
    end
`ifdef POWER_GATING
    else begin
      // CLKOUT mux
      if (RELEASE_ISO_FROM_SLEEP_CTRL===`IO_HOLD) begin
        assert #0 (CLKOUT===CLKIN) else $error("CLKOUT should follow CLKIN in IO_HOLD");
      end
      else if (RELEASE_ISO_FROM_SLEEP_CTRL!==`IO_HOLD) begin
        assert #0 (CLKOUT===CLKOUT_FROM_BUS) else $error("CLKOUT should follow CLKOUT_FROM_BUS when not IO_HOLD");
      end

      // DOUT priority + mux
      if (EXTERNAL_INT===1'b1) begin
        assert #0 (DOUT===1'b0) else $error("DOUT must be 0 when EXTERNAL_INT=1");
      end
      else if (EXTERNAL_INT===1'b0 && RELEASE_ISO_FROM_SLEEP_CTRL===`IO_HOLD) begin
        assert #0 (DOUT===DIN) else $error("DOUT should follow DIN in IO_HOLD");
      end
      else if (EXTERNAL_INT===1'b0 && RELEASE_ISO_FROM_SLEEP_CTRL!==`IO_HOLD) begin
        assert #0 (DOUT===DOUT_FROM_BUS) else $error("DOUT should follow DOUT_FROM_BUS when not IO_HOLD");
      end
    end
`else
    else begin
      assert #0 (CLKOUT===CLKOUT_FROM_BUS) else $error("CLKOUT should follow CLKOUT_FROM_BUS");
      assert #0 (DOUT  ===DOUT_FROM_BUS)   else $error("DOUT should follow DOUT_FROM_BUS");
    end
`endif
  end

  // Functional coverage of each path
  cover property (@(negedge RESETn) (DOUT===1'b1 && CLKOUT===1'b1));

`ifdef POWER_GATING
  // IO_HOLD taken for CLKOUT
  cover property (@(posedge RELEASE_ISO_FROM_SLEEP_CTRL or negedge RELEASE_ISO_FROM_SLEEP_CTRL)
                  RESETn===1'b1 && RELEASE_ISO_FROM_SLEEP_CTRL===`IO_HOLD);

  // EXTERNAL_INT priority path for DOUT
  cover property (@(posedge EXTERNAL_INT) RESETn===1'b1 && EXTERNAL_INT===1'b1);

  // DIN pass-through path for DOUT while in IO_HOLD
  cover property (@(posedge DIN or negedge DIN)
                  RESETn===1'b1 && EXTERNAL_INT===1'b0 &&
                  RELEASE_ISO_FROM_SLEEP_CTRL===`IO_HOLD);

  // Bus pass-through paths
  cover property (@(posedge DOUT_FROM_BUS or negedge DOUT_FROM_BUS)
                  RESETn===1'b1 && EXTERNAL_INT===1'b0 &&
                  RELEASE_ISO_FROM_SLEEP_CTRL!==`IO_HOLD);

  cover property (@(posedge CLKOUT_FROM_BUS or negedge CLKOUT_FROM_BUS)
                  RESETn===1'b1 && RELEASE_ISO_FROM_SLEEP_CTRL!==`IO_HOLD);

  // Priority corner: EXTERNAL_INT while IO_HOLD
  cover property (@(posedge EXTERNAL_INT)
                  RESETn===1'b1 && EXTERNAL_INT===1'b1 &&
                  RELEASE_ISO_FROM_SLEEP_CTRL===`IO_HOLD);
`else
  cover property (@(posedge DOUT_FROM_BUS or negedge DOUT_FROM_BUS) RESETn===1'b1);
  cover property (@(posedge CLKOUT_FROM_BUS or negedge CLKOUT_FROM_BUS) RESETn===1'b1);
`endif

endmodule

// Bind into DUT
bind mbus_wire_ctrl mbus_wire_ctrl_asserts mbus_wire_ctrl_asserts_i (
  .RESETn(RESETn),
  .DOUT_FROM_BUS(DOUT_FROM_BUS),
  .CLKOUT_FROM_BUS(CLKOUT_FROM_BUS),
`ifdef POWER_GATING
  .DIN(DIN),
  .CLKIN(CLKIN),
  .RELEASE_ISO_FROM_SLEEP_CTRL(RELEASE_ISO_FROM_SLEEP_CTRL),
  .EXTERNAL_INT(EXTERNAL_INT),
`endif
  .DOUT(DOUT),
  .CLKOUT(CLKOUT)
);

`endif // MBUS_WIRE_CTRL_SVA