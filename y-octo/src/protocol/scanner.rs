use super::*;

pub struct SyncMessageScanner<'a> {
    buffer: &'a [u8],
}

impl SyncMessageScanner<'_> {
    pub fn new(buffer: &[u8]) -> SyncMessageScanner<'_> {
        SyncMessageScanner { buffer }
    }
}

impl<'a> Iterator for SyncMessageScanner<'a> {
    type Item = Result<SyncMessage, nom::Err<nom::error::Error<&'a [u8]>>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.buffer.is_empty() {
            return None;
        }

        match read_sync_message(self.buffer) {
            Ok((tail, message)) => {
                self.buffer = tail;
                Some(Ok(message))
            }
            Err(nom::Err::Incomplete(_))
            | Err(nom::Err::Error(nom::error::Error {
                code: nom::error::ErrorKind::Eof,
                ..
            }))
            | Err(nom::Err::Failure(nom::error::Error {
                code: nom::error::ErrorKind::Eof,
                ..
            })) => {
                debug!("incomplete sync message");
                // nothing more can be read from this buffer
                self.buffer = &[];
                None
            }

            Err(e) => {
                // A malformed message has no known length, so the rest of the
                // buffer cannot be framed: stop after reporting it instead of
                // returning the same error forever.
                self.buffer = &[];
                Some(Err(e))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use proptest::{collection::vec, prelude::*};

    use super::*;

    proptest! {
        #[test]
        #[cfg_attr(miri, ignore)]
        fn test_sync_message_scanner(messages in vec(any::<SyncMessage>(), 0..10)) {
            let mut buffer = Vec::new();

            for message in &messages {
                write_sync_message(&mut buffer, message).unwrap();
            }

            let result: Result<Vec<SyncMessage>, _> = SyncMessageScanner::new(&buffer).collect();
            assert_eq!(result.unwrap(), messages);
        }
    }

    #[test]
    fn test_sync_message_scanner_stops_after_error() {
        let mut buffer = Vec::new();
        write_sync_message(&mut buffer, &SyncMessage::AwarenessQuery).unwrap();
        // an unknown message tag cannot be framed
        buffer.extend_from_slice(&[0x7f, 0x01, 0x02]);
        write_sync_message(&mut buffer, &SyncMessage::AwarenessQuery).unwrap();

        let mut scanner = SyncMessageScanner::new(&buffer);
        assert_eq!(scanner.next().unwrap().unwrap(), SyncMessage::AwarenessQuery);
        assert!(scanner.next().unwrap().is_err());
        // a `for` loop over the scanner terminates
        assert!(scanner.next().is_none());
        assert!(scanner.next().is_none());
    }
}
