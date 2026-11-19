use std::{env, error::Error};

use reqwest::blocking::Client;
use serde_json::{Value, json};

#[derive(Debug)]
struct TelegramConfig {
    endpoint: String,
    bot_token: String,
    chat_id: Option<String>,
}

fn string_field(value: &Value, names: &[&str]) -> Option<String> {
    names
        .iter()
        .find_map(|name| value.get(name)?.as_str())
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(ToOwned::to_owned)
}

fn parse_key_value_secret(secret: &str) -> Result<TelegramConfig, Box<dyn Error>> {
    let mut endpoint = None;
    let mut bot_token = None;
    let mut chat_id = None;

    for part in secret.split(['\n', ';']).map(str::trim).filter(|part| !part.is_empty()) {
        let Some((key, value)) = part.split_once('=') else {
            continue;
        };
        let value = value.trim();
        match key.trim() {
            "endpoint" | "TG_ENDPOINT" | "TELEGRAM_ENDPOINT" => {
                endpoint = Some(value.to_string());
            }
            "bot_token" | "token" | "TG_BOT_TOKEN" | "TELEGRAM_BOT_TOKEN" => {
                bot_token = Some(value.to_string());
            }
            "chat_id" | "TG_CHAT_ID" | "TELEGRAM_CHAT_ID" => {
                chat_id = Some(value.to_string());
            }
            _ => {}
        }
    }

    Ok(TelegramConfig {
        endpoint: endpoint.ok_or("telegram endpoint is missing")?,
        bot_token: bot_token.ok_or("telegram bot token is missing")?,
        chat_id,
    })
}

fn parse_secret(secret: &str) -> Result<TelegramConfig, Box<dyn Error>> {
    if let Ok(value) = serde_json::from_str::<Value>(secret) {
        return Ok(TelegramConfig {
            endpoint: string_field(&value, &["endpoint", "tg_endpoint", "telegram_endpoint"])
                .ok_or("telegram endpoint is missing")?,
            bot_token: string_field(&value, &["bot_token", "token", "tg_bot_token", "telegram_bot_token"])
                .ok_or("telegram bot token is missing")?,
            chat_id: string_field(&value, &["chat_id", "tg_chat_id", "telegram_chat_id"]),
        });
    }

    parse_key_value_secret(secret)
}

fn send_message(config: TelegramConfig, text: &str) -> Result<(), Box<dyn Error>> {
    let endpoint = config.endpoint.trim_end_matches('/');
    let url = if endpoint.contains("{token}") {
        endpoint.replace("{token}", &config.bot_token)
    } else if endpoint.contains("/bot") || endpoint.ends_with("/sendMessage") {
        endpoint.to_string()
    } else {
        format!("{endpoint}/bot{}/sendMessage", config.bot_token)
    };

    let mut payload = json!({
        "text": text,
        "disable_web_page_preview": true,
    });
    if let Some(chat_id) = config.chat_id {
        payload["chat_id"] = json!(chat_id);
    } else if !url.contains("chat_id=") {
        return Err("telegram chat_id is missing".into());
    }

    let response = Client::builder()
        .user_agent("y-octo-fuzz-notifier")
        .build()?
        .post(url)
        .json(&payload)
        .send()?;

    if !response.status().is_success() {
        return Err(format!("telegram request failed with {}", response.status()).into());
    }

    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let Some(secret) = env::var("TG_NOTIFY_SECRET")
        .ok()
        .filter(|secret| !secret.trim().is_empty())
    else {
        eprintln!("TG_NOTIFY_SECRET is empty; skipping Telegram notification.");
        return Ok(());
    };

    let text = env::args()
        .nth(1)
        .or_else(|| env::var("TG_NOTIFY_TEXT").ok())
        .ok_or("notification text is missing")?;
    let config = parse_secret(&secret)?;
    send_message(config, &text)
}
