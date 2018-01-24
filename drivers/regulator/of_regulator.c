/*
 * OF helpers for regulator framework
 *
 * Copyright (C) 2011 Texas Instruments, Inc.
 * Rajendra Nayak <rnayak@ti.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 */

#include <linux/module.h>
#include <linux/slab.h>
#include <linux/of.h>
#include <linux/regulator/machine.h>
#include <linux/regulator/driver.h>
#include <linux/regulator/of_regulator.h>

#include "internal.h"

static const char *const regulator_states[PM_SUSPEND_MAX + 1] = {
	[PM_SUSPEND_MEM]	= "regulator-state-mem",
	[PM_SUSPEND_MAX]	= "regulator-state-disk",
};

static void of_get_regulation_constraints(struct device_node *np,
					struct regulator_init_data **init_data
#if !defined(CONFIG_ARCH_MSM8916)
                                        ,
					const struct regulator_desc *desc
#endif
                                        )
{
	struct regulation_constraints *constraints = &(*init_data)->constraints;
	struct regulator_state *suspend_state;
	struct device_node *suspend_np;
	int ret, i;
	u32 pval;

	constraints->name = of_get_property(np, "regulator-name", NULL);

	if (!of_property_read_u32(np, "regulator-min-microvolt", &pval))
		constraints->min_uV = pval;

	if (!of_property_read_u32(np, "regulator-max-microvolt", &pval))
		constraints->max_uV = pval;

	/* Voltage change possible? */
	if (constraints->min_uV != constraints->max_uV)
		constraints->valid_ops_mask |= REGULATOR_CHANGE_VOLTAGE;

	/* Do we have a voltage range, if so try to apply it? */
	if (constraints->min_uV && constraints->max_uV)
		constraints->apply_uV = true;

	if (!of_property_read_u32(np, "regulator-microvolt-offset", &pval))
		constraints->uV_offset = pval;
	if (!of_property_read_u32(np, "regulator-min-microamp", &pval))
		constraints->min_uA = pval;
	if (!of_property_read_u32(np, "regulator-max-microamp", &pval))
		constraints->max_uA = pval;

	if (!of_property_read_u32(np, "regulator-input-current-limit-microamp",
				  &pval))
		constraints->ilim_uA = pval;

	/* Current change possible? */
	if (constraints->min_uA != constraints->max_uA)
		constraints->valid_ops_mask |= REGULATOR_CHANGE_CURRENT;

	constraints->boot_on = of_property_read_bool(np, "regulator-boot-on");
	constraints->always_on = of_property_read_bool(np, "regulator-always-on");
	if (!constraints->always_on) /* status change should be possible. */
		constraints->valid_ops_mask |= REGULATOR_CHANGE_STATUS;

	constraints->pull_down = of_property_read_bool(np, "regulator-pull-down");

	if (of_property_read_bool(np, "regulator-allow-bypass"))
		constraints->valid_ops_mask |= REGULATOR_CHANGE_BYPASS;

	if (of_property_read_bool(np, "regulator-allow-set-load"))
		constraints->valid_ops_mask |= REGULATOR_CHANGE_DRMS;

	ret = of_property_read_u32(np, "regulator-ramp-delay", &pval);
	if (!ret) {
		if (pval)
			constraints->ramp_delay = pval;
		else
			constraints->ramp_disable = true;
	}

	ret = of_property_read_u32(np, "regulator-enable-ramp-delay", &pval);
	if (!ret)
		constraints->enable_time = pval;

	constraints->soft_start = of_property_read_bool(np,
					"regulator-soft-start");
	ret = of_property_read_u32(np, "regulator-active-discharge", &pval);
	if (!ret) {
		constraints->active_discharge =
				(pval) ? REGULATOR_ACTIVE_DISCHARGE_ENABLE :
					REGULATOR_ACTIVE_DISCHARGE_DISABLE;
	}

	if (!of_property_read_u32(np, "regulator-initial-mode", &pval)) {
#if !defined(CONFIG_ARCH_MSM8916)
		if (desc && desc->of_map_mode) {
			ret = desc->of_map_mode(pval);
			if (ret == -EINVAL)
				pr_err("%s: invalid mode %u\n", np->name, pval);
			else
				constraints->initial_mode = ret;
		} else {
			pr_warn("%s: mapping for mode %d not defined\n",
				np->name, pval);
		}
#endif
	}

	if (!of_property_read_u32(np, "regulator-system-load", &pval))
		constraints->system_load = pval;

	constraints->over_current_protection = of_property_read_bool(np,
					"regulator-over-current-protection");

	for (i = 0; i < ARRAY_SIZE(regulator_states); i++) {
		switch (i) {
		case PM_SUSPEND_MEM:
			suspend_state = &constraints->state_mem;
			break;
		case PM_SUSPEND_MAX:
			suspend_state = &constraints->state_disk;
			break;
		case PM_SUSPEND_ON:
		case PM_SUSPEND_FREEZE:
		case PM_SUSPEND_STANDBY:
		default:
			continue;
		}

		suspend_np = of_get_child_by_name(np, regulator_states[i]);
		if (!suspend_np || !suspend_state)
			continue;

		if (!of_property_read_u32(suspend_np, "regulator-mode",
					  &pval)) {
#if !defined(CONFIG_ARCH_MSM8916)
			if (desc && desc->of_map_mode) {
				ret = desc->of_map_mode(pval);
				if (ret == -EINVAL)
					pr_err("%s: invalid mode %u\n",
					       np->name, pval);
				else
					suspend_state->mode = ret;
			} else {
				pr_warn("%s: mapping for mode %d not defined\n",
					np->name, pval);
			}
#endif
		}

		if (of_property_read_bool(suspend_np,
					"regulator-on-in-suspend"))
			suspend_state->enabled = true;
		else if (of_property_read_bool(suspend_np,
					"regulator-off-in-suspend"))
			suspend_state->disabled = true;

		if (!of_property_read_u32(suspend_np,
					"regulator-suspend-microvolt", &pval))
			suspend_state->uV = pval;

		if (i == PM_SUSPEND_MEM)
			constraints->initial_state = PM_SUSPEND_MEM;

		of_node_put(suspend_np);
		suspend_state = NULL;
		suspend_np = NULL;
	}
}


static const char *consumer_supply_prop_name = "qcom,consumer-supplies";
#define MAX_DEV_NAME_LEN 256
/*
 * Fill in regulator init_data based on qcom legacy requirements.
 */
static int of_get_qcom_regulator_init_data(struct device *dev,
					struct regulator_init_data **init_data)
{
	struct device_node *node = dev->of_node;
	struct regulator_consumer_supply *consumer_supplies;
	int i, rc, num_consumer_supplies, array_len;

	array_len = of_property_count_strings(node, consumer_supply_prop_name);
	if (array_len > 0) {
		/* Array length must be divisible by 2. */
		if (array_len & 1) {
			dev_err(dev, "error: %s device node property value "
				"contains an odd number of elements: %d\n",
				consumer_supply_prop_name, array_len);
			return -EINVAL;
		}
		num_consumer_supplies = array_len / 2;

		consumer_supplies = devm_kzalloc(dev,
			sizeof(struct regulator_consumer_supply)
			* num_consumer_supplies, GFP_KERNEL);
		if (consumer_supplies == NULL) {
			dev_err(dev, "devm_kzalloc failed\n");
			return -ENOMEM;
		}

		for (i = 0; i < num_consumer_supplies; i++) {
			rc = of_property_read_string_index(node,
				consumer_supply_prop_name, i * 2,
				&consumer_supplies[i].supply);
			if (rc) {
				dev_err(dev, "of_property_read_string_index "
					"failed, rc=%d\n", rc);
				devm_kfree(dev, consumer_supplies);
				return rc;
			}

			rc = of_property_read_string_index(node,
				consumer_supply_prop_name, (i * 2) + 1,
				&consumer_supplies[i].dev_name);
			if (rc) {
				dev_err(dev, "of_property_read_string_index "
					"failed, rc=%d\n", rc);
				devm_kfree(dev, consumer_supplies);
				return rc;
			}

			/* Treat dev_name = "" as a wildcard. */
			if (strnlen(consumer_supplies[i].dev_name,
					MAX_DEV_NAME_LEN) == 0)
				consumer_supplies[i].dev_name = NULL;
		}

		(*init_data)->consumer_supplies = consumer_supplies;
		(*init_data)->num_consumer_supplies = num_consumer_supplies;
	}

	return 0;
}

/**
 * of_get_regulator_init_data - extract regulator_init_data structure info
 * @dev: device requesting for regulator_init_data
 * @node: regulator device node
 * @desc: regulator description
 *
 * Populates regulator_init_data structure by extracting data from device
 * tree node, returns a pointer to the populated struture or NULL if memory
 * alloc fails.
 */
#if !defined(CONFIG_ARCH_MSM8916)
struct regulator_init_data *of_get_regulator_init_data(struct device *dev,
					  struct device_node *node,
					  const struct regulator_desc *desc)
#else
struct regulator_init_data *of_get_regulator_init_data(struct device *dev,
						struct device_node *node)
#endif
{
	struct regulator_init_data *init_data;
#if defined(CONFIG_ARCH_MSM8916)
	int rc;
#endif

	if (!node)
		return NULL;

	init_data = devm_kzalloc(dev, sizeof(*init_data), GFP_KERNEL);
	if (!init_data)
		return NULL; /* Out of memory? */

#if !defined(CONFIG_ARCH_MSM8916)
	of_get_regulation_constraints(node, &init_data, desc);
#else
    of_get_regulation_constraints(node, &init_data);
	rc = of_get_qcom_regulator_init_data(dev, &init_data);
	if (rc) {
		devm_kfree(dev, init_data);
		return NULL;
	}
#endif
	return init_data;
}
EXPORT_SYMBOL_GPL(of_get_regulator_init_data);

struct devm_of_regulator_matches {
	struct of_regulator_match *matches;
	unsigned int num_matches;
};

static void devm_of_regulator_put_matches(struct device *dev, void *res)
{
	struct devm_of_regulator_matches *devm_matches = res;
	int i;

	for (i = 0; i < devm_matches->num_matches; i++)
		of_node_put(devm_matches->matches[i].of_node);
}

/**
 * of_regulator_match - extract multiple regulator init data from device tree.
 * @dev: device requesting the data
 * @node: parent device node of the regulators
 * @matches: match table for the regulators
 * @num_matches: number of entries in match table
 *
 * This function uses a match table specified by the regulator driver to
 * parse regulator init data from the device tree. @node is expected to
 * contain a set of child nodes, each providing the init data for one
 * regulator. The data parsed from a child node will be matched to a regulator
 * based on either the deprecated property regulator-compatible if present,
 * or otherwise the child node's name. Note that the match table is modified
 * in place and an additional of_node reference is taken for each matched
 * regulator.
 *
 * Returns the number of matches found or a negative error code on failure.
 */
int of_regulator_match(struct device *dev, struct device_node *node,
		       struct of_regulator_match *matches,
		       unsigned int num_matches)
{
	unsigned int count = 0;
	unsigned int i;
	const char *name;
	struct device_node *child;
	struct devm_of_regulator_matches *devm_matches;

	if (!dev || !node)
		return -EINVAL;

	devm_matches = devres_alloc(devm_of_regulator_put_matches,
				    sizeof(struct devm_of_regulator_matches),
				    GFP_KERNEL);
	if (!devm_matches)
		return -ENOMEM;

	devm_matches->matches = matches;
	devm_matches->num_matches = num_matches;

	devres_add(dev, devm_matches);

	for (i = 0; i < num_matches; i++) {
		struct of_regulator_match *match = &matches[i];
		match->init_data = NULL;
		match->of_node = NULL;
	}

	for_each_child_of_node(node, child) {
		name = of_get_property(child,
					"regulator-compatible", NULL);
		if (!name)
			name = child->name;
		for (i = 0; i < num_matches; i++) {
			struct of_regulator_match *match = &matches[i];
			if (match->of_node)
				continue;

			if (strcmp(match->name, name))
				continue;

			match->init_data =
				of_get_regulator_init_data(dev, child
#if !defined(CONFIG_ARCH_MSM8916)
						, match->desc
#endif
						);
			if (!match->init_data) {
				dev_err(dev,
					"failed to parse DT for regulator %s\n",
					child->name);
				return -EINVAL;
			}
			match->of_node = of_node_get(child);
			count++;
			break;
		}
	}

	return count;
}
EXPORT_SYMBOL_GPL(of_regulator_match);

struct regulator_init_data *regulator_of_get_init_data(struct device *dev,
					    const struct regulator_desc *desc,
					    struct regulator_config *config,
					    struct device_node **node)
{
	struct device_node *search, *child;
	struct regulator_init_data *init_data = NULL;
	const char *name;

	if (!dev->of_node || !desc->of_match)
		return NULL;

	if (desc->regulators_node)
		search = of_get_child_by_name(dev->of_node,
					      desc->regulators_node);
	else
		search = dev->of_node;

	if (!search) {
		dev_dbg(dev, "Failed to find regulator container node '%s'\n",
			desc->regulators_node);
		return NULL;
	}

	for_each_available_child_of_node(search, child) {
		name = of_get_property(child, "regulator-compatible", NULL);
		if (!name)
			name = child->name;

		if (strcmp(desc->of_match, name))
			continue;

		init_data = of_get_regulator_init_data(dev, child
#if !defined(CONFIG_ARCH_MSM8916)
				, desc
#endif
				);
		if (!init_data) {
			dev_err(dev,
				"failed to parse DT for regulator %s\n",
				child->name);
			break;
		}

		if (desc->of_parse_cb) {
			if (desc->of_parse_cb(child, desc, config)) {
				dev_err(dev,
					"driver callback failed to parse DT for regulator %s\n",
					child->name);
				init_data = NULL;
				break;
			}
		}

		of_node_get(child);
		*node = child;
		break;
	}

	of_node_put(search);

	return init_data;
}
